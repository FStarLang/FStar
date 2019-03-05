open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____65150 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____65186 -> false
  
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
                    let uu____65610 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____65610;
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
                     (let uu___656_65642 = wl  in
                      {
                        attempting = (uu___656_65642.attempting);
                        wl_deferred = (uu___656_65642.wl_deferred);
                        ctr = (uu___656_65642.ctr);
                        defer_ok = (uu___656_65642.defer_ok);
                        smt_ok = (uu___656_65642.smt_ok);
                        umax_heuristic_ok =
                          (uu___656_65642.umax_heuristic_ok);
                        tcenv = (uu___656_65642.tcenv);
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
            let uu___662_65675 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___662_65675.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___662_65675.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___662_65675.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___662_65675.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___662_65675.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___662_65675.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___662_65675.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___662_65675.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___662_65675.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___662_65675.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___662_65675.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___662_65675.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___662_65675.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___662_65675.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___662_65675.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___662_65675.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___662_65675.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___662_65675.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___662_65675.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___662_65675.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___662_65675.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___662_65675.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___662_65675.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___662_65675.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___662_65675.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___662_65675.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___662_65675.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___662_65675.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___662_65675.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___662_65675.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___662_65675.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___662_65675.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___662_65675.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___662_65675.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___662_65675.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___662_65675.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___662_65675.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___662_65675.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___662_65675.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___662_65675.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___662_65675.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___662_65675.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____65677 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____65677 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____65720 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____65757 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____65791 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____65802 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____65813 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___585_65831  ->
    match uu___585_65831 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____65843 = FStar_Syntax_Util.head_and_args t  in
    match uu____65843 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____65906 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____65908 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____65923 =
                     let uu____65925 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____65925  in
                   FStar_Util.format1 "@<%s>" uu____65923
                in
             let uu____65929 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____65906 uu____65908 uu____65929
         | uu____65932 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___586_65944  ->
      match uu___586_65944 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____65949 =
            let uu____65953 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____65955 =
              let uu____65959 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____65961 =
                let uu____65965 =
                  let uu____65969 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____65969]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____65965
                 in
              uu____65959 :: uu____65961  in
            uu____65953 :: uu____65955  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____65949
      | FStar_TypeChecker_Common.CProb p ->
          let uu____65980 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____65982 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____65984 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____65980
            uu____65982 (rel_to_string p.FStar_TypeChecker_Common.relation)
            uu____65984
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___587_65998  ->
      match uu___587_65998 with
      | UNIV (u,t) ->
          let x =
            let uu____66004 = FStar_Options.hide_uvar_nums ()  in
            if uu____66004
            then "?"
            else
              (let uu____66011 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____66011 FStar_Util.string_of_int)
             in
          let uu____66015 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____66015
      | TERM (u,t) ->
          let x =
            let uu____66022 = FStar_Options.hide_uvar_nums ()  in
            if uu____66022
            then "?"
            else
              (let uu____66029 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____66029 FStar_Util.string_of_int)
             in
          let uu____66033 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____66033
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____66052 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____66052 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____66073 =
      let uu____66077 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____66077
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____66073 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____66096 .
    (FStar_Syntax_Syntax.term * 'Auu____66096) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____66115 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____66136  ->
              match uu____66136 with
              | (x,uu____66143) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____66115 (FStar_String.concat " ")
  
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
        (let uu____66186 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____66186
         then
           let uu____66191 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____66191
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___588_66202  ->
    match uu___588_66202 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____66208 .
    'Auu____66208 FStar_TypeChecker_Common.problem ->
      'Auu____66208 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___722_66220 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___722_66220.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___722_66220.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___722_66220.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___722_66220.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___722_66220.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___722_66220.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___722_66220.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____66228 .
    'Auu____66228 FStar_TypeChecker_Common.problem ->
      'Auu____66228 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___589_66248  ->
    match uu___589_66248 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _66254  -> FStar_TypeChecker_Common.TProb _66254)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _66260  -> FStar_TypeChecker_Common.CProb _66260)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___590_66266  ->
    match uu___590_66266 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___734_66272 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___734_66272.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___734_66272.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___734_66272.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___734_66272.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___734_66272.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___734_66272.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___734_66272.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___734_66272.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___734_66272.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___738_66280 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___738_66280.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___738_66280.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___738_66280.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___738_66280.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___738_66280.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___738_66280.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___738_66280.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___738_66280.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___738_66280.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___591_66293  ->
      match uu___591_66293 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___592_66300  ->
    match uu___592_66300 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___593_66313  ->
    match uu___593_66313 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___594_66328  ->
    match uu___594_66328 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___595_66343  ->
    match uu___595_66343 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___596_66357  ->
    match uu___596_66357 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___597_66371  ->
    match uu___597_66371 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___598_66383  ->
    match uu___598_66383 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____66399 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____66399) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____66429 =
          let uu____66431 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66431  in
        if uu____66429
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____66468)::bs ->
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
          let uu____66515 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____66539 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____66539]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____66515
      | FStar_TypeChecker_Common.CProb p ->
          let uu____66567 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____66591 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____66591]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____66567
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____66638 =
          let uu____66640 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66640  in
        if uu____66638
        then ()
        else
          (let uu____66645 =
             let uu____66648 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____66648
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____66645 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____66697 =
          let uu____66699 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66699  in
        if uu____66697
        then ()
        else
          (let uu____66704 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____66704)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____66724 =
        let uu____66726 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____66726  in
      if uu____66724
      then ()
      else
        (let msgf m =
           let uu____66740 =
             let uu____66742 =
               let uu____66744 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____66744 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____66742  in
           Prims.op_Hat msg uu____66740  in
         (let uu____66749 = msgf "scope"  in
          let uu____66752 = p_scope prob  in
          def_scope_wf uu____66749 (p_loc prob) uu____66752);
         (let uu____66764 = msgf "guard"  in
          def_check_scoped uu____66764 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____66771 = msgf "lhs"  in
                def_check_scoped uu____66771 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____66774 = msgf "rhs"  in
                def_check_scoped uu____66774 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____66781 = msgf "lhs"  in
                def_check_scoped_comp uu____66781 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____66784 = msgf "rhs"  in
                def_check_scoped_comp uu____66784 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___831_66805 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___831_66805.wl_deferred);
          ctr = (uu___831_66805.ctr);
          defer_ok = (uu___831_66805.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___831_66805.umax_heuristic_ok);
          tcenv = (uu___831_66805.tcenv);
          wl_implicits = (uu___831_66805.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____66813 .
    FStar_TypeChecker_Env.env ->
      ('Auu____66813 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___835_66836 = empty_worklist env  in
      let uu____66837 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____66837;
        wl_deferred = (uu___835_66836.wl_deferred);
        ctr = (uu___835_66836.ctr);
        defer_ok = (uu___835_66836.defer_ok);
        smt_ok = (uu___835_66836.smt_ok);
        umax_heuristic_ok = (uu___835_66836.umax_heuristic_ok);
        tcenv = (uu___835_66836.tcenv);
        wl_implicits = (uu___835_66836.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___840_66860 = wl  in
        {
          attempting = (uu___840_66860.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___840_66860.ctr);
          defer_ok = (uu___840_66860.defer_ok);
          smt_ok = (uu___840_66860.smt_ok);
          umax_heuristic_ok = (uu___840_66860.umax_heuristic_ok);
          tcenv = (uu___840_66860.tcenv);
          wl_implicits = (uu___840_66860.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___845_66888 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___845_66888.wl_deferred);
         ctr = (uu___845_66888.ctr);
         defer_ok = (uu___845_66888.defer_ok);
         smt_ok = (uu___845_66888.smt_ok);
         umax_heuristic_ok = (uu___845_66888.umax_heuristic_ok);
         tcenv = (uu___845_66888.tcenv);
         wl_implicits = (uu___845_66888.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____66902 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____66902 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____66936 = FStar_Syntax_Util.type_u ()  in
            match uu____66936 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____66948 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____66948 with
                 | (uu____66966,tt,wl1) ->
                     let uu____66969 = FStar_Syntax_Util.mk_eq2 u tt t1 t2
                        in
                     (uu____66969, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___599_66975  ->
    match uu___599_66975 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _66981  -> FStar_TypeChecker_Common.TProb _66981) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _66987  -> FStar_TypeChecker_Common.CProb _66987) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____66995 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____66995 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____67015  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____67112 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____67112 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____67112 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____67112 FStar_TypeChecker_Common.problem *
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
                        let uu____67199 =
                          let uu____67208 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____67208]  in
                        FStar_List.append scope uu____67199
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____67251 =
                      let uu____67254 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____67254  in
                    FStar_List.append uu____67251
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____67273 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____67273 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____67299 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____67299;
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
                  (let uu____67373 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____67373 with
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
                  (let uu____67461 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____67461 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____67499 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____67499 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____67499 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____67499 FStar_TypeChecker_Common.problem *
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
                          let uu____67567 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____67567]  in
                        let uu____67586 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____67586
                     in
                  let uu____67589 =
                    let uu____67596 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___928_67607 = wl  in
                       {
                         attempting = (uu___928_67607.attempting);
                         wl_deferred = (uu___928_67607.wl_deferred);
                         ctr = (uu___928_67607.ctr);
                         defer_ok = (uu___928_67607.defer_ok);
                         smt_ok = (uu___928_67607.smt_ok);
                         umax_heuristic_ok =
                           (uu___928_67607.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___928_67607.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____67596
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____67589 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____67625 =
                              let uu____67630 =
                                let uu____67631 =
                                  let uu____67640 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____67640
                                   in
                                [uu____67631]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____67630
                               in
                            uu____67625 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____67670 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____67670;
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
                let uu____67718 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____67718;
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
  'Auu____67733 .
    worklist ->
      'Auu____67733 FStar_TypeChecker_Common.problem ->
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
              let uu____67766 =
                let uu____67769 =
                  let uu____67770 =
                    let uu____67777 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____67777)  in
                  FStar_Syntax_Syntax.NT uu____67770  in
                [uu____67769]  in
              FStar_Syntax_Subst.subst uu____67766 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____67801 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____67801
        then
          let uu____67809 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____67812 = prob_to_string env d  in
          let uu____67814 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____67809 uu____67812 uu____67814 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____67830 -> failwith "impossible"  in
           let uu____67833 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____67849 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____67851 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____67849, uu____67851)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____67858 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____67860 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____67858, uu____67860)
              in
           match uu____67833 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___600_67888  ->
            match uu___600_67888 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____67900 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____67904 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____67904 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___601_67935  ->
           match uu___601_67935 with
           | UNIV uu____67938 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____67945 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____67945
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
        (fun uu___602_67973  ->
           match uu___602_67973 with
           | UNIV (u',t) ->
               let uu____67978 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____67978
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____67985 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____67997 =
        let uu____67998 =
          let uu____67999 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____67999
           in
        FStar_Syntax_Subst.compress uu____67998  in
      FStar_All.pipe_right uu____67997 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____68011 =
        let uu____68012 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____68012  in
      FStar_All.pipe_right uu____68011 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____68020 = FStar_Syntax_Util.head_and_args t  in
    match uu____68020 with
    | (h,uu____68039) ->
        let uu____68064 =
          let uu____68065 = FStar_Syntax_Subst.compress h  in
          uu____68065.FStar_Syntax_Syntax.n  in
        (match uu____68064 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____68070 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____68083 = should_strongly_reduce t  in
      if uu____68083
      then
        let uu____68086 =
          let uu____68087 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____68087  in
        FStar_All.pipe_right uu____68086 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____68097 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____68097) ->
        (FStar_Syntax_Syntax.term * 'Auu____68097)
  =
  fun env  ->
    fun t  ->
      let uu____68120 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____68120, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____68172  ->
              match uu____68172 with
              | (x,imp) ->
                  let uu____68191 =
                    let uu___1025_68192 = x  in
                    let uu____68193 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1025_68192.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1025_68192.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____68193
                    }  in
                  (uu____68191, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____68217 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____68217
        | FStar_Syntax_Syntax.U_max us ->
            let uu____68221 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____68221
        | uu____68224 -> u2  in
      let uu____68225 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____68225
  
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
                (let uu____68346 = norm_refinement env t12  in
                 match uu____68346 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____68361;
                     FStar_Syntax_Syntax.vars = uu____68362;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____68386 =
                       let uu____68388 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____68390 = FStar_Syntax_Print.tag_of_term tt
                          in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____68388 uu____68390
                        in
                     failwith uu____68386)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____68406 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____68406
          | FStar_Syntax_Syntax.Tm_uinst uu____68407 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68444 =
                   let uu____68445 = FStar_Syntax_Subst.compress t1'  in
                   uu____68445.FStar_Syntax_Syntax.n  in
                 match uu____68444 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68460 -> aux true t1'
                 | uu____68468 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____68483 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68514 =
                   let uu____68515 = FStar_Syntax_Subst.compress t1'  in
                   uu____68515.FStar_Syntax_Syntax.n  in
                 match uu____68514 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68530 -> aux true t1'
                 | uu____68538 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____68553 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68600 =
                   let uu____68601 = FStar_Syntax_Subst.compress t1'  in
                   uu____68601.FStar_Syntax_Syntax.n  in
                 match uu____68600 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68616 -> aux true t1'
                 | uu____68624 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____68639 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____68654 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____68669 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____68684 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____68699 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____68728 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____68761 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____68782 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____68809 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____68837 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____68874 ->
              let uu____68881 =
                let uu____68883 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68885 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68883 uu____68885
                 in
              failwith uu____68881
          | FStar_Syntax_Syntax.Tm_ascribed uu____68900 ->
              let uu____68927 =
                let uu____68929 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68931 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68929 uu____68931
                 in
              failwith uu____68927
          | FStar_Syntax_Syntax.Tm_delayed uu____68946 ->
              let uu____68969 =
                let uu____68971 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68973 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68971 uu____68973
                 in
              failwith uu____68969
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____68988 =
                let uu____68990 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68992 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68990 uu____68992
                 in
              failwith uu____68988
           in
        let uu____69007 = whnf env t1  in aux false uu____69007
  
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
      let uu____69068 = base_and_refinement env t  in
      FStar_All.pipe_right uu____69068 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____69109 = FStar_Syntax_Syntax.null_bv t  in
    (uu____69109, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____69136 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____69136 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____69196  ->
    match uu____69196 with
    | (t_base,refopt) ->
        let uu____69227 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____69227 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____69269 =
      let uu____69273 =
        let uu____69276 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____69303  ->
                  match uu____69303 with | (uu____69312,uu____69313,x) -> x))
           in
        FStar_List.append wl.attempting uu____69276  in
      FStar_List.map (wl_prob_to_string wl) uu____69273  in
    FStar_All.pipe_right uu____69269 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____69336 .
    ('Auu____69336 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____69348  ->
    match uu____69348 with
    | (uu____69355,c,args) ->
        let uu____69358 = print_ctx_uvar c  in
        let uu____69360 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____69358 uu____69360
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____69370 = FStar_Syntax_Util.head_and_args t  in
    match uu____69370 with
    | (head1,_args) ->
        let uu____69414 =
          let uu____69415 = FStar_Syntax_Subst.compress head1  in
          uu____69415.FStar_Syntax_Syntax.n  in
        (match uu____69414 with
         | FStar_Syntax_Syntax.Tm_uvar uu____69419 -> true
         | uu____69433 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____69441 = FStar_Syntax_Util.head_and_args t  in
    match uu____69441 with
    | (head1,_args) ->
        let uu____69484 =
          let uu____69485 = FStar_Syntax_Subst.compress head1  in
          uu____69485.FStar_Syntax_Syntax.n  in
        (match uu____69484 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____69489) -> u
         | uu____69506 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____69531 = FStar_Syntax_Util.head_and_args t  in
      match uu____69531 with
      | (head1,args) ->
          let uu____69578 =
            let uu____69579 = FStar_Syntax_Subst.compress head1  in
            uu____69579.FStar_Syntax_Syntax.n  in
          (match uu____69578 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____69587)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____69620 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___603_69645  ->
                         match uu___603_69645 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____69650 =
                               let uu____69651 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____69651.FStar_Syntax_Syntax.n  in
                             (match uu____69650 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____69656 -> false)
                         | uu____69658 -> true))
                  in
               (match uu____69620 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____69683 =
                        FStar_List.collect
                          (fun uu___604_69695  ->
                             match uu___604_69695 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____69699 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____69699]
                             | uu____69700 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____69683 FStar_List.rev  in
                    let uu____69723 =
                      let uu____69730 =
                        let uu____69739 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___605_69761  ->
                                  match uu___605_69761 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____69765 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____69765]
                                  | uu____69766 -> []))
                           in
                        FStar_All.pipe_right uu____69739 FStar_List.rev  in
                      let uu____69789 =
                        let uu____69792 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____69792  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____69730 uu____69789
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____69723 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____69828  ->
                                match uu____69828 with
                                | (x,i) ->
                                    let uu____69847 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____69847, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____69878  ->
                                match uu____69878 with
                                | (a,i) ->
                                    let uu____69897 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____69897, i)) args_sol
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
           | uu____69919 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____69941 =
          let uu____69964 =
            let uu____69965 = FStar_Syntax_Subst.compress k  in
            uu____69965.FStar_Syntax_Syntax.n  in
          match uu____69964 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____70047 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____70047)
              else
                (let uu____70082 = FStar_Syntax_Util.abs_formals t  in
                 match uu____70082 with
                 | (ys',t1,uu____70115) ->
                     let uu____70120 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____70120))
          | uu____70159 ->
              let uu____70160 =
                let uu____70165 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____70165)  in
              ((ys, t), uu____70160)
           in
        match uu____69941 with
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
                 let uu____70260 = FStar_Syntax_Util.rename_binders xs ys1
                    in
                 FStar_Syntax_Subst.subst_comp uu____70260 c  in
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
               (let uu____70338 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____70338
                then
                  let uu____70343 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____70345 = print_ctx_uvar uv  in
                  let uu____70347 = FStar_Syntax_Print.term_to_string phi1
                     in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____70343 uu____70345 uu____70347
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____70356 =
                   let uu____70358 = FStar_Util.string_of_int (p_pid prob)
                      in
                   Prims.op_Hat "solve_prob'.sol." uu____70358  in
                 let uu____70361 =
                   let uu____70364 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____70364
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____70356 uu____70361 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____70397 =
               let uu____70398 =
                 let uu____70400 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____70402 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____70400 uu____70402
                  in
               failwith uu____70398  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____70468  ->
                       match uu____70468 with
                       | (a,i) ->
                           let uu____70489 =
                             let uu____70490 = FStar_Syntax_Subst.compress a
                                in
                             uu____70490.FStar_Syntax_Syntax.n  in
                           (match uu____70489 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____70516 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____70526 =
                 let uu____70528 = is_flex g  in
                 Prims.op_Negation uu____70528  in
               if uu____70526
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____70537 = destruct_flex_t g wl  in
                  match uu____70537 with
                  | ((uu____70542,uv1,args),wl1) ->
                      ((let uu____70547 = args_as_binders args  in
                        assign_solution uu____70547 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___1277_70549 = wl1  in
              {
                attempting = (uu___1277_70549.attempting);
                wl_deferred = (uu___1277_70549.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___1277_70549.defer_ok);
                smt_ok = (uu___1277_70549.smt_ok);
                umax_heuristic_ok = (uu___1277_70549.umax_heuristic_ok);
                tcenv = (uu___1277_70549.tcenv);
                wl_implicits = (uu___1277_70549.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____70574 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____70574
         then
           let uu____70579 = FStar_Util.string_of_int pid  in
           let uu____70581 =
             let uu____70583 = FStar_List.map (uvi_to_string wl.tcenv) sol
                in
             FStar_All.pipe_right uu____70583 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____70579
             uu____70581
         else ());
        commit sol;
        (let uu___1285_70597 = wl  in
         {
           attempting = (uu___1285_70597.attempting);
           wl_deferred = (uu___1285_70597.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___1285_70597.defer_ok);
           smt_ok = (uu___1285_70597.smt_ok);
           umax_heuristic_ok = (uu___1285_70597.umax_heuristic_ok);
           tcenv = (uu___1285_70597.tcenv);
           wl_implicits = (uu___1285_70597.wl_implicits)
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
             | (uu____70663,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____70691 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____70691
              in
           (let uu____70697 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____70697
            then
              let uu____70702 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____70706 =
                let uu____70708 =
                  FStar_List.map (uvi_to_string wl.tcenv) uvis  in
                FStar_All.pipe_right uu____70708 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____70702
                uu____70706
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
        let uu____70743 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____70743 FStar_Util.set_elements  in
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
      let uu____70783 = occurs uk t  in
      match uu____70783 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____70822 =
                 let uu____70824 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____70826 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____70824 uu____70826
                  in
               FStar_Pervasives_Native.Some uu____70822)
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
            let uu____70946 = maximal_prefix bs_tail bs'_tail  in
            (match uu____70946 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____70997 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____71054  ->
             match uu____71054 with
             | (x,uu____71066) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____71084 = FStar_List.last bs  in
      match uu____71084 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____71108) ->
          let uu____71119 =
            FStar_Util.prefix_until
              (fun uu___606_71134  ->
                 match uu___606_71134 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____71137 -> false) g
             in
          (match uu____71119 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____71151,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____71188 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____71188 with
        | (pfx,uu____71198) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____71210 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____71210 with
             | (uu____71218,src',wl1) ->
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
                 | uu____71332 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____71333 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____71397  ->
                  fun uu____71398  ->
                    match (uu____71397, uu____71398) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____71501 =
                          let uu____71503 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____71503
                           in
                        if uu____71501
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____71537 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____71537
                           then
                             let uu____71554 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____71554)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____71333 with | (isect,uu____71604) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____71640 'Auu____71641 .
    (FStar_Syntax_Syntax.bv * 'Auu____71640) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____71641) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____71699  ->
              fun uu____71700  ->
                match (uu____71699, uu____71700) with
                | ((a,uu____71719),(b,uu____71721)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____71737 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____71737) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____71768  ->
           match uu____71768 with
           | (y,uu____71775) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____71785 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____71785) Prims.list ->
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
                   let uu____71947 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____71947
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____71980 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____72032 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____72077 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____72099 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___607_72107  ->
    match uu___607_72107 with
    | MisMatch (d1,d2) ->
        let uu____72119 =
          let uu____72121 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____72123 =
            let uu____72125 =
              let uu____72127 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____72127 ")"  in
            Prims.op_Hat ") (" uu____72125  in
          Prims.op_Hat uu____72121 uu____72123  in
        Prims.op_Hat "MisMatch (" uu____72119
    | HeadMatch u ->
        let uu____72134 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____72134
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___608_72143  ->
    match uu___608_72143 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____72160 -> HeadMatch false
  
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
          let uu____72182 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____72182 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____72193 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____72217 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____72227 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____72254 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____72254
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____72255 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____72256 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____72257 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____72270 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____72284 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____72308) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____72314,uu____72315) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____72357) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____72382;
             FStar_Syntax_Syntax.index = uu____72383;
             FStar_Syntax_Syntax.sort = t2;_},uu____72385)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____72393 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____72394 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____72395 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____72410 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____72417 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____72437 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____72437
  
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
           { FStar_Syntax_Syntax.blob = uu____72456;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____72457;
             FStar_Syntax_Syntax.ltyp = uu____72458;
             FStar_Syntax_Syntax.rng = uu____72459;_},uu____72460)
            ->
            let uu____72471 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____72471 t21
        | (uu____72472,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____72473;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____72474;
             FStar_Syntax_Syntax.ltyp = uu____72475;
             FStar_Syntax_Syntax.rng = uu____72476;_})
            ->
            let uu____72487 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____72487
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____72499 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____72499
            then FullMatch
            else
              (let uu____72504 =
                 let uu____72513 =
                   let uu____72516 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____72516  in
                 let uu____72517 =
                   let uu____72520 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____72520  in
                 (uu____72513, uu____72517)  in
               MisMatch uu____72504)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____72526),FStar_Syntax_Syntax.Tm_uinst (g,uu____72528)) ->
            let uu____72537 = head_matches env f g  in
            FStar_All.pipe_right uu____72537 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____72538) -> HeadMatch true
        | (uu____72540,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____72544 = FStar_Const.eq_const c d  in
            if uu____72544
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____72554),FStar_Syntax_Syntax.Tm_uvar (uv',uu____72556)) ->
            let uu____72589 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____72589
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____72599),FStar_Syntax_Syntax.Tm_refine (y,uu____72601)) ->
            let uu____72610 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____72610 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____72612),uu____72613) ->
            let uu____72618 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____72618 head_match
        | (uu____72619,FStar_Syntax_Syntax.Tm_refine (x,uu____72621)) ->
            let uu____72626 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____72626 head_match
        | (FStar_Syntax_Syntax.Tm_type
           uu____72627,FStar_Syntax_Syntax.Tm_type uu____72628) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____72630,FStar_Syntax_Syntax.Tm_arrow uu____72631) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____72662),FStar_Syntax_Syntax.Tm_app
           (head',uu____72664)) ->
            let uu____72713 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____72713 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____72715),uu____72716) ->
            let uu____72741 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____72741 head_match
        | (uu____72742,FStar_Syntax_Syntax.Tm_app (head1,uu____72744)) ->
            let uu____72769 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____72769 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____72770,FStar_Syntax_Syntax.Tm_let
           uu____72771) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____72799,FStar_Syntax_Syntax.Tm_match uu____72800) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____72846,FStar_Syntax_Syntax.Tm_abs
           uu____72847) -> HeadMatch true
        | uu____72885 ->
            let uu____72890 =
              let uu____72899 = delta_depth_of_term env t11  in
              let uu____72902 = delta_depth_of_term env t21  in
              (uu____72899, uu____72902)  in
            MisMatch uu____72890
  
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
            (let uu____72968 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____72968
             then
               let uu____72973 = FStar_Syntax_Print.term_to_string t  in
               let uu____72975 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____72973 uu____72975
             else ());
            (let uu____72980 =
               let uu____72981 = FStar_Syntax_Util.un_uinst head1  in
               uu____72981.FStar_Syntax_Syntax.n  in
             match uu____72980 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____72987 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____72987 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____73001 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____73001
                        then
                          let uu____73006 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____73006
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____73011 ->
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
                      let uu____73028 =
                        let uu____73030 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____73030 = FStar_Syntax_Util.Equal  in
                      if uu____73028
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____73037 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____73037
                          then
                            let uu____73042 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____73044 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n"
                              uu____73042 uu____73044
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____73049 -> FStar_Pervasives_Native.None)
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
            (let uu____73201 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____73201
             then
               let uu____73206 = FStar_Syntax_Print.term_to_string t11  in
               let uu____73208 = FStar_Syntax_Print.term_to_string t21  in
               let uu____73210 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____73206
                 uu____73208 uu____73210
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____73238 =
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
               match uu____73238 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____73286 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____73286 with
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
                  uu____73324),uu____73325)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____73346 =
                      let uu____73355 = maybe_inline t11  in
                      let uu____73358 = maybe_inline t21  in
                      (uu____73355, uu____73358)  in
                    match uu____73346 with
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
                 (uu____73401,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____73402))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____73423 =
                      let uu____73432 = maybe_inline t11  in
                      let uu____73435 = maybe_inline t21  in
                      (uu____73432, uu____73435)  in
                    match uu____73423 with
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
             | MisMatch uu____73490 -> fail1 n_delta r t11 t21
             | uu____73499 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____73514 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____73514
           then
             let uu____73519 = FStar_Syntax_Print.term_to_string t1  in
             let uu____73521 = FStar_Syntax_Print.term_to_string t2  in
             let uu____73523 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____73531 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____73548 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____73548
                    (fun uu____73583  ->
                       match uu____73583 with
                       | (t11,t21) ->
                           let uu____73591 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____73593 =
                             let uu____73595 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____73595  in
                           Prims.op_Hat uu____73591 uu____73593))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____73519 uu____73521 uu____73523 uu____73531
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____73612 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____73612 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___609_73627  ->
    match uu___609_73627 with
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
      let uu___1789_73676 = p  in
      let uu____73679 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____73680 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1789_73676.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____73679;
        FStar_TypeChecker_Common.relation =
          (uu___1789_73676.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____73680;
        FStar_TypeChecker_Common.element =
          (uu___1789_73676.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1789_73676.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1789_73676.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1789_73676.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1789_73676.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1789_73676.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____73695 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____73695
            (fun _73700  -> FStar_TypeChecker_Common.TProb _73700)
      | FStar_TypeChecker_Common.CProb uu____73701 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____73724 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____73724 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____73732 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____73732 with
           | (lh,lhs_args) ->
               let uu____73779 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____73779 with
                | (rh,rhs_args) ->
                    let uu____73826 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73839,FStar_Syntax_Syntax.Tm_uvar uu____73840)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____73929 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____73956,uu____73957)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____73972,FStar_Syntax_Syntax.Tm_uvar uu____73973)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73988,FStar_Syntax_Syntax.Tm_arrow
                         uu____73989) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_74019 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_74019.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_74019.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_74019.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_74019.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_74019.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_74019.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_74019.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_74019.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_74019.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____74022,FStar_Syntax_Syntax.Tm_type uu____74023)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_74039 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_74039.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_74039.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_74039.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_74039.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_74039.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_74039.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_74039.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_74039.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_74039.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____74042,FStar_Syntax_Syntax.Tm_uvar uu____74043)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_74059 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_74059.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_74059.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_74059.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_74059.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_74059.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_74059.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_74059.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_74059.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_74059.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____74062,FStar_Syntax_Syntax.Tm_uvar uu____74063)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____74078,uu____74079)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____74094,FStar_Syntax_Syntax.Tm_uvar uu____74095)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____74110,uu____74111) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____73826 with
                     | (rank,tp1) ->
                         let uu____74124 =
                           FStar_All.pipe_right
                             (let uu___1860_74128 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1860_74128.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1860_74128.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1860_74128.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1860_74128.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1860_74128.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1860_74128.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1860_74128.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1860_74128.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1860_74128.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _74131  ->
                                FStar_TypeChecker_Common.TProb _74131)
                            in
                         (rank, uu____74124))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____74135 =
            FStar_All.pipe_right
              (let uu___1864_74139 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1864_74139.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1864_74139.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1864_74139.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1864_74139.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1864_74139.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1864_74139.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1864_74139.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1864_74139.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1864_74139.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _74142  -> FStar_TypeChecker_Common.CProb _74142)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____74135)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____74202 probs =
      match uu____74202 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____74283 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____74304 = rank wl.tcenv hd1  in
               (match uu____74304 with
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
                      (let uu____74365 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____74370 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____74370)
                          in
                       if uu____74365
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
          let uu____74443 = FStar_Syntax_Util.head_and_args t  in
          match uu____74443 with
          | (hd1,uu____74462) ->
              let uu____74487 =
                let uu____74488 = FStar_Syntax_Subst.compress hd1  in
                uu____74488.FStar_Syntax_Syntax.n  in
              (match uu____74487 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____74493) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____74528  ->
                           match uu____74528 with
                           | (y,uu____74537) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____74560  ->
                                       match uu____74560 with
                                       | (x,uu____74569) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____74574 -> false)
           in
        let uu____74576 = rank tcenv p  in
        match uu____74576 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____74585 -> true
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
    match projectee with | UDeferred _0 -> true | uu____74622 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____74642 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____74663 -> false
  
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
                        let uu____74726 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____74726 with
                        | (k,uu____74734) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____74747 -> false)))
            | uu____74749 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____74801 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____74809 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____74809 = (Prims.parse_int "0")))
                           in
                        if uu____74801 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____74830 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____74838 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____74838 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____74830)
               in
            let uu____74842 = filter1 u12  in
            let uu____74845 = filter1 u22  in (uu____74842, uu____74845)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____74880 = filter_out_common_univs us1 us2  in
                   (match uu____74880 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____74940 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____74940 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____74943 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____74954 =
                             let uu____74956 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____74958 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____74956 uu____74958
                              in
                           UFailed uu____74954))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____74984 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____74984 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____75010 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____75010 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____75013 ->
                   let uu____75018 =
                     let uu____75020 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____75022 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)"
                       uu____75020 uu____75022 msg
                      in
                   UFailed uu____75018)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____75025,uu____75026) ->
              let uu____75028 =
                let uu____75030 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75032 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75030 uu____75032
                 in
              failwith uu____75028
          | (FStar_Syntax_Syntax.U_unknown ,uu____75035) ->
              let uu____75036 =
                let uu____75038 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75040 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75038 uu____75040
                 in
              failwith uu____75036
          | (uu____75043,FStar_Syntax_Syntax.U_bvar uu____75044) ->
              let uu____75046 =
                let uu____75048 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75050 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75048 uu____75050
                 in
              failwith uu____75046
          | (uu____75053,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____75054 =
                let uu____75056 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75058 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75056 uu____75058
                 in
              failwith uu____75054
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____75088 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____75088
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____75105 = occurs_univ v1 u3  in
              if uu____75105
              then
                let uu____75108 =
                  let uu____75110 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____75112 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____75110 uu____75112
                   in
                try_umax_components u11 u21 uu____75108
              else
                (let uu____75117 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____75117)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____75129 = occurs_univ v1 u3  in
              if uu____75129
              then
                let uu____75132 =
                  let uu____75134 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____75136 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____75134 uu____75136
                   in
                try_umax_components u11 u21 uu____75132
              else
                (let uu____75141 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____75141)
          | (FStar_Syntax_Syntax.U_max uu____75142,uu____75143) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____75151 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____75151
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____75157,FStar_Syntax_Syntax.U_max uu____75158) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____75166 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____75166
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____75172,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____75174,FStar_Syntax_Syntax.U_name uu____75175) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____75177) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____75179) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____75181,FStar_Syntax_Syntax.U_succ uu____75182) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____75184,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____75291 = bc1  in
      match uu____75291 with
      | (bs1,mk_cod1) ->
          let uu____75335 = bc2  in
          (match uu____75335 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____75446 = aux xs ys  in
                     (match uu____75446 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____75529 =
                       let uu____75536 = mk_cod1 xs  in ([], uu____75536)  in
                     let uu____75539 =
                       let uu____75546 = mk_cod2 ys  in ([], uu____75546)  in
                     (uu____75529, uu____75539)
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
                  let uu____75615 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____75615 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____75618 =
                    let uu____75619 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____75619 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____75618
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____75624 = has_type_guard t1 t2  in (uu____75624, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____75625 = has_type_guard t2 t1  in (uu____75625, wl)
  
let is_flex_pat :
  'Auu____75635 'Auu____75636 'Auu____75637 .
    ('Auu____75635 * 'Auu____75636 * 'Auu____75637 Prims.list) -> Prims.bool
  =
  fun uu___610_75651  ->
    match uu___610_75651 with
    | (uu____75660,uu____75661,[]) -> true
    | uu____75665 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____75698 = f  in
      match uu____75698 with
      | (uu____75705,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____75706;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____75707;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____75710;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____75711;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____75712;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____75713;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____75783  ->
                 match uu____75783 with
                 | (y,uu____75792) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____75946 =
                  let uu____75961 =
                    let uu____75964 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____75964  in
                  ((FStar_List.rev pat_binders), uu____75961)  in
                FStar_Pervasives_Native.Some uu____75946
            | (uu____75997,[]) ->
                let uu____76028 =
                  let uu____76043 =
                    let uu____76046 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____76046  in
                  ((FStar_List.rev pat_binders), uu____76043)  in
                FStar_Pervasives_Native.Some uu____76028
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____76137 =
                  let uu____76138 = FStar_Syntax_Subst.compress a  in
                  uu____76138.FStar_Syntax_Syntax.n  in
                (match uu____76137 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____76158 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____76158
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___2188_76188 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___2188_76188.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___2188_76188.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____76192 =
                            let uu____76193 =
                              let uu____76200 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____76200)  in
                            FStar_Syntax_Syntax.NT uu____76193  in
                          [uu____76192]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___2194_76216 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2194_76216.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2194_76216.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____76217 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____76257 =
                  let uu____76272 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____76272  in
                (match uu____76257 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____76347 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____76380 ->
               let uu____76381 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____76381 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____76703 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____76703
       then
         let uu____76708 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____76708
       else ());
      (let uu____76713 = next_prob probs  in
       match uu____76713 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___2219_76740 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___2219_76740.wl_deferred);
               ctr = (uu___2219_76740.ctr);
               defer_ok = (uu___2219_76740.defer_ok);
               smt_ok = (uu___2219_76740.smt_ok);
               umax_heuristic_ok = (uu___2219_76740.umax_heuristic_ok);
               tcenv = (uu___2219_76740.tcenv);
               wl_implicits = (uu___2219_76740.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____76749 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____76749
                 then
                   let uu____76752 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____76752
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
                           (let uu___2231_76764 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___2231_76764.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___2231_76764.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___2231_76764.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___2231_76764.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___2231_76764.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___2231_76764.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___2231_76764.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___2231_76764.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___2231_76764.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____76790 ->
                let uu____76801 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____76872  ->
                          match uu____76872 with
                          | (c,uu____76883,uu____76884) -> c < probs.ctr))
                   in
                (match uu____76801 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____76939 =
                            let uu____76944 =
                              FStar_List.map
                                (fun uu____76962  ->
                                   match uu____76962 with
                                   | (uu____76976,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____76944, (probs.wl_implicits))  in
                          Success uu____76939
                      | uu____76984 ->
                          let uu____76995 =
                            let uu___2249_76996 = probs  in
                            let uu____76997 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____77020  ->
                                      match uu____77020 with
                                      | (uu____77029,uu____77030,y) -> y))
                               in
                            {
                              attempting = uu____76997;
                              wl_deferred = rest;
                              ctr = (uu___2249_76996.ctr);
                              defer_ok = (uu___2249_76996.defer_ok);
                              smt_ok = (uu___2249_76996.smt_ok);
                              umax_heuristic_ok =
                                (uu___2249_76996.umax_heuristic_ok);
                              tcenv = (uu___2249_76996.tcenv);
                              wl_implicits = (uu___2249_76996.wl_implicits)
                            }  in
                          solve env uu____76995))))

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
            let uu____77041 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____77041 with
            | USolved wl1 ->
                let uu____77043 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____77043
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
                  let uu____77097 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____77097 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____77100 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____77113;
                  FStar_Syntax_Syntax.vars = uu____77114;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____77117;
                  FStar_Syntax_Syntax.vars = uu____77118;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____77131,uu____77132) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____77140,FStar_Syntax_Syntax.Tm_uinst uu____77141) ->
                failwith "Impossible: expect head symbols to match"
            | uu____77149 -> USolved wl

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
            ((let uu____77161 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____77161
              then
                let uu____77166 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____77166 msg
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
               let uu____77258 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____77258 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____77313 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____77313
                then
                  let uu____77318 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____77320 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____77318 uu____77320
                else ());
               (let uu____77325 = head_matches_delta env1 wl2 t1 t2  in
                match uu____77325 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____77371 = eq_prob t1 t2 wl2  in
                         (match uu____77371 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____77392 ->
                         let uu____77401 = eq_prob t1 t2 wl2  in
                         (match uu____77401 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____77451 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____77466 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____77467 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____77466, uu____77467)
                           | FStar_Pervasives_Native.None  ->
                               let uu____77472 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____77473 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____77472, uu____77473)
                            in
                         (match uu____77451 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____77504 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____77504 with
                                | (t1_hd,t1_args) ->
                                    let uu____77549 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____77549 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____77615 =
                                              let uu____77622 =
                                                let uu____77633 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____77633 :: t1_args  in
                                              let uu____77650 =
                                                let uu____77659 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____77659 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____77708  ->
                                                   fun uu____77709  ->
                                                     fun uu____77710  ->
                                                       match (uu____77708,
                                                               uu____77709,
                                                               uu____77710)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____77760),
                                                          (a2,uu____77762))
                                                           ->
                                                           let uu____77799 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____77799
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____77622
                                                uu____77650
                                               in
                                            match uu____77615 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___2403_77825 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___2403_77825.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___2403_77825.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___2403_77825.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____77837 =
                                                  solve env1 wl'  in
                                                (match uu____77837 with
                                                 | Success (uu____77840,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___2412_77844
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___2412_77844.attempting);
                                                            wl_deferred =
                                                              (uu___2412_77844.wl_deferred);
                                                            ctr =
                                                              (uu___2412_77844.ctr);
                                                            defer_ok =
                                                              (uu___2412_77844.defer_ok);
                                                            smt_ok =
                                                              (uu___2412_77844.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___2412_77844.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___2412_77844.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____77845 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____77878 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____77878 with
                                | (t1_base,p1_opt) ->
                                    let uu____77914 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____77914 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____78013 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____78013
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
                                               let uu____78066 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____78066
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
                                               let uu____78098 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____78098
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
                                               let uu____78130 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____78130
                                           | uu____78133 -> t_base  in
                                         let uu____78150 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____78150 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____78164 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____78164, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____78171 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____78171 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____78207 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____78207 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____78243 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____78243
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
                              let uu____78267 = combine t11 t21 wl2  in
                              (match uu____78267 with
                               | (t12,ps,wl3) ->
                                   ((let uu____78300 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____78300
                                     then
                                       let uu____78305 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____78305
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____78347 ts1 =
               match uu____78347 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____78410 = pairwise out t wl2  in
                        (match uu____78410 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____78446 =
               let uu____78457 = FStar_List.hd ts  in (uu____78457, [], wl1)
                in
             let uu____78466 = FStar_List.tl ts  in
             aux uu____78446 uu____78466  in
           let uu____78473 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____78473 with
           | (this_flex,this_rigid) ->
               let uu____78499 =
                 let uu____78500 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____78500.FStar_Syntax_Syntax.n  in
               (match uu____78499 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____78525 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____78525
                    then
                      let uu____78528 = destruct_flex_t this_flex wl  in
                      (match uu____78528 with
                       | (flex,wl1) ->
                           let uu____78535 = quasi_pattern env flex  in
                           (match uu____78535 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____78554 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____78554
                                  then
                                    let uu____78559 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____78559
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____78566 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2514_78569 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2514_78569.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2514_78569.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2514_78569.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2514_78569.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2514_78569.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2514_78569.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2514_78569.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2514_78569.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2514_78569.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____78566)
                | uu____78570 ->
                    ((let uu____78572 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____78572
                      then
                        let uu____78577 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____78577
                      else ());
                     (let uu____78582 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____78582 with
                      | (u,_args) ->
                          let uu____78625 =
                            let uu____78626 = FStar_Syntax_Subst.compress u
                               in
                            uu____78626.FStar_Syntax_Syntax.n  in
                          (match uu____78625 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____78654 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____78654 with
                                 | (u',uu____78673) ->
                                     let uu____78698 =
                                       let uu____78699 = whnf env u'  in
                                       uu____78699.FStar_Syntax_Syntax.n  in
                                     (match uu____78698 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____78721 -> false)
                                  in
                               let uu____78723 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___611_78746  ->
                                         match uu___611_78746 with
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
                                              | uu____78760 -> false)
                                         | uu____78764 -> false))
                                  in
                               (match uu____78723 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____78779 = whnf env this_rigid
                                         in
                                      let uu____78780 =
                                        FStar_List.collect
                                          (fun uu___612_78786  ->
                                             match uu___612_78786 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____78792 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____78792]
                                             | uu____78796 -> [])
                                          bounds_probs
                                         in
                                      uu____78779 :: uu____78780  in
                                    let uu____78797 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____78797 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____78830 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____78845 =
                                               let uu____78846 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____78846.FStar_Syntax_Syntax.n
                                                in
                                             match uu____78845 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____78858 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____78858)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____78869 -> bound  in
                                           let uu____78870 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____78870)  in
                                         (match uu____78830 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____78905 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____78905
                                                then
                                                  let wl'1 =
                                                    let uu___2574_78911 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2574_78911.wl_deferred);
                                                      ctr =
                                                        (uu___2574_78911.ctr);
                                                      defer_ok =
                                                        (uu___2574_78911.defer_ok);
                                                      smt_ok =
                                                        (uu___2574_78911.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2574_78911.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2574_78911.tcenv);
                                                      wl_implicits =
                                                        (uu___2574_78911.wl_implicits)
                                                    }  in
                                                  let uu____78912 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____78912
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____78918 =
                                                  solve_t env eq_prob
                                                    (let uu___2579_78920 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2579_78920.wl_deferred);
                                                       ctr =
                                                         (uu___2579_78920.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2579_78920.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2579_78920.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2579_78920.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____78918 with
                                                | Success (uu____78922,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2585_78925 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2585_78925.wl_deferred);
                                                        ctr =
                                                          (uu___2585_78925.ctr);
                                                        defer_ok =
                                                          (uu___2585_78925.defer_ok);
                                                        smt_ok =
                                                          (uu___2585_78925.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2585_78925.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2585_78925.tcenv);
                                                        wl_implicits =
                                                          (uu___2585_78925.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2588_78927 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2588_78927.attempting);
                                                        wl_deferred =
                                                          (uu___2588_78927.wl_deferred);
                                                        ctr =
                                                          (uu___2588_78927.ctr);
                                                        defer_ok =
                                                          (uu___2588_78927.defer_ok);
                                                        smt_ok =
                                                          (uu___2588_78927.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2588_78927.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2588_78927.tcenv);
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
                                                    let uu____78943 =
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
                                                    ((let uu____78957 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____78957
                                                      then
                                                        let uu____78962 =
                                                          let uu____78964 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____78964
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____78962
                                                      else ());
                                                     (let uu____78977 =
                                                        let uu____78992 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____78992)
                                                         in
                                                      match uu____78977 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____79014))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____79040 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____79040
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
                                                                  let uu____79060
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____79060))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____79085 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____79085
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
                                                                    let uu____79105
                                                                    =
                                                                    let uu____79110
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____79110
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____79105
                                                                    [] wl2
                                                                     in
                                                                  let uu____79116
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____79116))))
                                                      | uu____79117 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____79133 when flip ->
                               let uu____79134 =
                                 let uu____79136 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____79138 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____79136 uu____79138
                                  in
                               failwith uu____79134
                           | uu____79141 ->
                               let uu____79142 =
                                 let uu____79144 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____79146 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____79144 uu____79146
                                  in
                               failwith uu____79142)))))

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
                      (fun uu____79182  ->
                         match uu____79182 with
                         | (x,i) ->
                             let uu____79201 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____79201, i)) bs_lhs
                     in
                  let uu____79204 = lhs  in
                  match uu____79204 with
                  | (uu____79205,u_lhs,uu____79207) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____79304 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____79314 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____79314, univ)
                             in
                          match uu____79304 with
                          | (k,univ) ->
                              let uu____79321 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____79321 with
                               | (uu____79338,u,wl3) ->
                                   let uu____79341 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____79341, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____79367 =
                              let uu____79380 =
                                let uu____79391 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____79391 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____79442  ->
                                   fun uu____79443  ->
                                     match (uu____79442, uu____79443) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____79544 =
                                           let uu____79551 =
                                             let uu____79554 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____79554
                                              in
                                           copy_uvar u_lhs [] uu____79551 wl2
                                            in
                                         (match uu____79544 with
                                          | (uu____79583,t_a,wl3) ->
                                              let uu____79586 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____79586 with
                                               | (uu____79605,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____79380
                                ([], wl1)
                               in
                            (match uu____79367 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2698_79661 = ct  in
                                   let uu____79662 =
                                     let uu____79665 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____79665
                                      in
                                   let uu____79680 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2698_79661.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2698_79661.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____79662;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____79680;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2698_79661.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2701_79698 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2701_79698.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2701_79698.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____79701 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____79701 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____79763 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____79763 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____79774 =
                                          let uu____79779 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____79779)  in
                                        TERM uu____79774  in
                                      let uu____79780 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____79780 with
                                       | (sub_prob,wl3) ->
                                           let uu____79794 =
                                             let uu____79795 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____79795
                                              in
                                           solve env uu____79794))
                             | (x,imp)::formals2 ->
                                 let uu____79817 =
                                   let uu____79824 =
                                     let uu____79827 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____79827
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____79824 wl1
                                    in
                                 (match uu____79817 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____79848 =
                                          let uu____79851 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____79851
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____79848 u_x
                                         in
                                      let uu____79852 =
                                        let uu____79855 =
                                          let uu____79858 =
                                            let uu____79859 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____79859, imp)  in
                                          [uu____79858]  in
                                        FStar_List.append bs_terms
                                          uu____79855
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____79852 formals2 wl2)
                              in
                           let uu____79886 = occurs_check u_lhs arrow1  in
                           (match uu____79886 with
                            | (uu____79899,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____79915 =
                                    let uu____79917 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____79917
                                     in
                                  giveup_or_defer env orig wl uu____79915
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
              (let uu____79950 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____79950
               then
                 let uu____79955 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____79958 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____79955 (rel_to_string (p_rel orig)) uu____79958
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____80085 = rhs wl1 scope env1 subst1  in
                     (match uu____80085 with
                      | (rhs_prob,wl2) ->
                          ((let uu____80106 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____80106
                            then
                              let uu____80111 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____80111
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____80189 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____80189 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2770_80191 = hd1  in
                       let uu____80192 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2770_80191.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2770_80191.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____80192
                       }  in
                     let hd21 =
                       let uu___2773_80196 = hd2  in
                       let uu____80197 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2773_80196.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2773_80196.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____80197
                       }  in
                     let uu____80200 =
                       let uu____80205 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____80205
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____80200 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____80226 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____80226
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____80233 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____80233 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____80300 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____80300
                                  in
                               ((let uu____80318 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____80318
                                 then
                                   let uu____80323 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____80325 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____80323
                                     uu____80325
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____80358 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____80394 = aux wl [] env [] bs1 bs2  in
               match uu____80394 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____80449 = attempt sub_probs wl2  in
                   solve env uu____80449)

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
            let uu___2808_80470 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2808_80470.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2808_80470.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____80483 = try_solve env wl'  in
          match uu____80483 with
          | Success (uu____80484,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2817_80488 = wl  in
                  {
                    attempting = (uu___2817_80488.attempting);
                    wl_deferred = (uu___2817_80488.wl_deferred);
                    ctr = (uu___2817_80488.ctr);
                    defer_ok = (uu___2817_80488.defer_ok);
                    smt_ok = (uu___2817_80488.smt_ok);
                    umax_heuristic_ok = (uu___2817_80488.umax_heuristic_ok);
                    tcenv = (uu___2817_80488.tcenv);
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
        (let uu____80500 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____80500 wl)

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
              let uu____80514 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____80514 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____80548 = lhs1  in
              match uu____80548 with
              | (uu____80551,ctx_u,uu____80553) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____80561 ->
                        let uu____80562 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____80562 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____80611 = quasi_pattern env1 lhs1  in
              match uu____80611 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____80645) ->
                  let uu____80650 = lhs1  in
                  (match uu____80650 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____80665 = occurs_check ctx_u rhs1  in
                       (match uu____80665 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____80716 =
                                let uu____80724 =
                                  let uu____80726 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____80726
                                   in
                                FStar_Util.Inl uu____80724  in
                              (uu____80716, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____80754 =
                                 let uu____80756 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____80756  in
                               if uu____80754
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____80783 =
                                    let uu____80791 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____80791  in
                                  let uu____80797 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____80783, uu____80797)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____80841 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____80841 with
              | (rhs_hd,args) ->
                  let uu____80884 = FStar_Util.prefix args  in
                  (match uu____80884 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____80956 = lhs1  in
                       (match uu____80956 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____80960 =
                              let uu____80971 =
                                let uu____80978 =
                                  let uu____80981 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____80981
                                   in
                                copy_uvar u_lhs [] uu____80978 wl1  in
                              match uu____80971 with
                              | (uu____81008,t_last_arg,wl2) ->
                                  let uu____81011 =
                                    let uu____81018 =
                                      let uu____81019 =
                                        let uu____81028 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____81028]  in
                                      FStar_List.append bs_lhs uu____81019
                                       in
                                    copy_uvar u_lhs uu____81018 t_res_lhs wl2
                                     in
                                  (match uu____81011 with
                                   | (uu____81063,lhs',wl3) ->
                                       let uu____81066 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____81066 with
                                        | (uu____81083,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____80960 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____81104 =
                                     let uu____81105 =
                                       let uu____81110 =
                                         let uu____81111 =
                                           let uu____81114 =
                                             let uu____81119 =
                                               let uu____81120 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____81120]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____81119
                                              in
                                           uu____81114
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____81111
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____81110)  in
                                     TERM uu____81105  in
                                   [uu____81104]  in
                                 let uu____81147 =
                                   let uu____81154 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____81154 with
                                   | (p1,wl3) ->
                                       let uu____81174 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____81174 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____81147 with
                                  | (sub_probs,wl3) ->
                                      let uu____81206 =
                                        let uu____81207 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____81207  in
                                      solve env1 uu____81206))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____81241 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____81241 with
                | (uu____81259,args) ->
                    (match args with | [] -> false | uu____81295 -> true)
                 in
              let is_arrow rhs2 =
                let uu____81314 =
                  let uu____81315 = FStar_Syntax_Subst.compress rhs2  in
                  uu____81315.FStar_Syntax_Syntax.n  in
                match uu____81314 with
                | FStar_Syntax_Syntax.Tm_arrow uu____81319 -> true
                | uu____81335 -> false  in
              let uu____81337 = quasi_pattern env1 lhs1  in
              match uu____81337 with
              | FStar_Pervasives_Native.None  ->
                  let uu____81348 =
                    let uu____81350 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____81350
                     in
                  giveup_or_defer env1 orig1 wl1 uu____81348
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____81359 = is_app rhs1  in
                  if uu____81359
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____81364 = is_arrow rhs1  in
                     if uu____81364
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____81369 =
                          let uu____81371 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____81371
                           in
                        giveup_or_defer env1 orig1 wl1 uu____81369))
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
                let uu____81382 = lhs  in
                (match uu____81382 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____81386 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____81386 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____81404 =
                              let uu____81408 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____81408
                               in
                            FStar_All.pipe_right uu____81404
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____81429 = occurs_check ctx_uv rhs1  in
                          (match uu____81429 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____81458 =
                                   let uu____81460 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____81460
                                    in
                                 giveup_or_defer env orig wl uu____81458
                               else
                                 (let uu____81466 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____81466
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____81473 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____81473
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____81477 =
                                         let uu____81479 =
                                           names_to_string1 fvs2  in
                                         let uu____81481 =
                                           names_to_string1 fvs1  in
                                         let uu____81483 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____81479 uu____81481
                                           uu____81483
                                          in
                                       giveup_or_defer env orig wl
                                         uu____81477)
                                    else first_order orig env wl lhs rhs1))
                      | uu____81495 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____81502 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____81502 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____81528 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____81528
                             | (FStar_Util.Inl msg,uu____81530) ->
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
                  (let uu____81575 =
                     let uu____81592 = quasi_pattern env lhs  in
                     let uu____81599 = quasi_pattern env rhs  in
                     (uu____81592, uu____81599)  in
                   match uu____81575 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____81642 = lhs  in
                       (match uu____81642 with
                        | ({ FStar_Syntax_Syntax.n = uu____81643;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____81645;_},u_lhs,uu____81647)
                            ->
                            let uu____81650 = rhs  in
                            (match uu____81650 with
                             | (uu____81651,u_rhs,uu____81653) ->
                                 let uu____81654 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____81654
                                 then
                                   let uu____81661 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____81661
                                 else
                                   (let uu____81664 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____81664 with
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
                                        let uu____81696 =
                                          let uu____81703 =
                                            let uu____81706 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____81706
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____81703
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____81696 with
                                         | (uu____81718,w,wl1) ->
                                             let w_app =
                                               let uu____81724 =
                                                 let uu____81729 =
                                                   FStar_List.map
                                                     (fun uu____81740  ->
                                                        match uu____81740
                                                        with
                                                        | (z,uu____81748) ->
                                                            let uu____81753 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____81753) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____81729
                                                  in
                                               uu____81724
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____81757 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____81757
                                               then
                                                 let uu____81762 =
                                                   let uu____81766 =
                                                     flex_t_to_string lhs  in
                                                   let uu____81768 =
                                                     let uu____81772 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____81774 =
                                                       let uu____81778 =
                                                         term_to_string w  in
                                                       let uu____81780 =
                                                         let uu____81784 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____81793 =
                                                           let uu____81797 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____81806 =
                                                             let uu____81810
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____81810]
                                                              in
                                                           uu____81797 ::
                                                             uu____81806
                                                            in
                                                         uu____81784 ::
                                                           uu____81793
                                                          in
                                                       uu____81778 ::
                                                         uu____81780
                                                        in
                                                     uu____81772 ::
                                                       uu____81774
                                                      in
                                                   uu____81766 :: uu____81768
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____81762
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____81827 =
                                                     let uu____81832 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____81832)  in
                                                   TERM uu____81827  in
                                                 let uu____81833 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____81833
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____81841 =
                                                        let uu____81846 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____81846)
                                                         in
                                                      TERM uu____81841  in
                                                    [s1; s2])
                                                  in
                                               let uu____81847 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____81847))))))
                   | uu____81848 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____81919 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____81919
            then
              let uu____81924 = FStar_Syntax_Print.term_to_string t1  in
              let uu____81926 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____81928 = FStar_Syntax_Print.term_to_string t2  in
              let uu____81930 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____81924 uu____81926 uu____81928 uu____81930
            else ());
           (let uu____81941 = FStar_Syntax_Util.head_and_args t1  in
            match uu____81941 with
            | (head1,args1) ->
                let uu____81984 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____81984 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____82054 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____82054 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____82084 =
                         let uu____82086 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____82088 = args_to_string args1  in
                         let uu____82092 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____82094 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____82086 uu____82088 uu____82092 uu____82094
                          in
                       giveup env1 uu____82084 orig
                     else
                       (let uu____82101 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____82110 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____82110 = FStar_Syntax_Util.Equal)
                           in
                        if uu____82101
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___3066_82114 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___3066_82114.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___3066_82114.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___3066_82114.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___3066_82114.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___3066_82114.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___3066_82114.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___3066_82114.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___3066_82114.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____82124 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____82124
                                    else solve env1 wl2))
                        else
                          (let uu____82129 = base_and_refinement env1 t1  in
                           match uu____82129 with
                           | (base1,refinement1) ->
                               let uu____82154 = base_and_refinement env1 t2
                                  in
                               (match uu____82154 with
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
                                           let uu____82319 =
                                             FStar_List.fold_right
                                               (fun uu____82359  ->
                                                  fun uu____82360  ->
                                                    match (uu____82359,
                                                            uu____82360)
                                                    with
                                                    | (((a1,uu____82412),
                                                        (a2,uu____82414)),
                                                       (probs,wl3)) ->
                                                        let uu____82463 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____82463
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____82319 with
                                           | (subprobs,wl3) ->
                                               ((let uu____82506 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____82506
                                                 then
                                                   let uu____82511 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____82511
                                                 else ());
                                                (let uu____82517 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____82517
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
                                                    (let uu____82544 =
                                                       mk_sub_probs wl3  in
                                                     match uu____82544 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____82560 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____82560
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____82568 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____82568))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____82592 =
                                                    mk_sub_probs wl3  in
                                                  match uu____82592 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____82606 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____82606)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____82632 =
                                           match uu____82632 with
                                           | (prob,reason) ->
                                               ((let uu____82643 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____82643
                                                 then
                                                   let uu____82648 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____82650 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____82648 uu____82650
                                                     reason
                                                 else ());
                                                (let uu____82655 =
                                                   let uu____82664 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____82667 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____82664, uu____82667)
                                                    in
                                                 match uu____82655 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____82680 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____82680 with
                                                      | (head1',uu____82698)
                                                          ->
                                                          let uu____82723 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____82723
                                                           with
                                                           | (head2',uu____82741)
                                                               ->
                                                               let uu____82766
                                                                 =
                                                                 let uu____82771
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____82772
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____82771,
                                                                   uu____82772)
                                                                  in
                                                               (match uu____82766
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____82774
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____82774
                                                                    then
                                                                    let uu____82779
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____82781
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____82783
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____82785
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____82779
                                                                    uu____82781
                                                                    uu____82783
                                                                    uu____82785
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____82790
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___3152_82798
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___3152_82798.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___3152_82798.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___3152_82798.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___3152_82798.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___3152_82798.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___3152_82798.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___3152_82798.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___3152_82798.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____82800
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____82800
                                                                    then
                                                                    let uu____82805
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____82805
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____82810 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____82822 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____82822 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____82830 =
                                             let uu____82831 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____82831.FStar_Syntax_Syntax.n
                                              in
                                           match uu____82830 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____82836 -> false  in
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
                                          | uu____82839 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____82842 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___3172_82878 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___3172_82878.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___3172_82878.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___3172_82878.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___3172_82878.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___3172_82878.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___3172_82878.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___3172_82878.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___3172_82878.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____82954 = destruct_flex_t scrutinee wl1  in
             match uu____82954 with
             | ((_t,uv,_args),wl2) ->
                 let uu____82965 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____82965 with
                  | (xs,pat_term,uu____82981,uu____82982) ->
                      let uu____82987 =
                        FStar_List.fold_left
                          (fun uu____83010  ->
                             fun x  ->
                               match uu____83010 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____83031 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____83031 with
                                    | (uu____83050,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____82987 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____83071 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____83071 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___3212_83088 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___3212_83088.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___3212_83088.umax_heuristic_ok);
                                    tcenv = (uu___3212_83088.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____83100 = solve env1 wl'  in
                                (match uu____83100 with
                                 | Success (uu____83103,imps) ->
                                     let wl'1 =
                                       let uu___3220_83106 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___3220_83106.wl_deferred);
                                         ctr = (uu___3220_83106.ctr);
                                         defer_ok =
                                           (uu___3220_83106.defer_ok);
                                         smt_ok = (uu___3220_83106.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___3220_83106.umax_heuristic_ok);
                                         tcenv = (uu___3220_83106.tcenv);
                                         wl_implicits =
                                           (uu___3220_83106.wl_implicits)
                                       }  in
                                     let uu____83107 = solve env1 wl'1  in
                                     (match uu____83107 with
                                      | Success (uu____83110,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___3228_83114 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___3228_83114.attempting);
                                                 wl_deferred =
                                                   (uu___3228_83114.wl_deferred);
                                                 ctr = (uu___3228_83114.ctr);
                                                 defer_ok =
                                                   (uu___3228_83114.defer_ok);
                                                 smt_ok =
                                                   (uu___3228_83114.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3228_83114.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3228_83114.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____83115 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____83122 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____83145 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____83145
                 then
                   let uu____83150 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____83152 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____83150 uu____83152
                 else ());
                (let uu____83157 =
                   let uu____83178 =
                     let uu____83187 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____83187)  in
                   let uu____83194 =
                     let uu____83203 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____83203)  in
                   (uu____83178, uu____83194)  in
                 match uu____83157 with
                 | ((uu____83233,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____83236;
                                   FStar_Syntax_Syntax.vars = uu____83237;_}),
                    (s,t)) ->
                     let uu____83308 =
                       let uu____83310 = is_flex scrutinee  in
                       Prims.op_Negation uu____83310  in
                     if uu____83308
                     then
                       ((let uu____83321 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____83321
                         then
                           let uu____83326 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____83326
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____83345 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____83345
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____83360 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____83360
                           then
                             let uu____83365 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____83367 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____83365 uu____83367
                           else ());
                          (let pat_discriminates uu___613_83392 =
                             match uu___613_83392 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____83408;
                                  FStar_Syntax_Syntax.p = uu____83409;_},FStar_Pervasives_Native.None
                                ,uu____83410) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____83424;
                                  FStar_Syntax_Syntax.p = uu____83425;_},FStar_Pervasives_Native.None
                                ,uu____83426) -> true
                             | uu____83453 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____83556 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____83556 with
                                       | (uu____83558,uu____83559,t') ->
                                           let uu____83577 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____83577 with
                                            | (FullMatch ,uu____83589) ->
                                                true
                                            | (HeadMatch
                                               uu____83603,uu____83604) ->
                                                true
                                            | uu____83619 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____83656 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____83656
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____83667 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____83667 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____83755,uu____83756) ->
                                       branches1
                                   | uu____83901 -> branches  in
                                 let uu____83956 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____83965 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____83965 with
                                        | (p,uu____83969,uu____83970) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _83999  -> FStar_Util.Inr _83999)
                                   uu____83956))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____84029 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____84029 with
                                | (p,uu____84038,e) ->
                                    ((let uu____84057 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____84057
                                      then
                                        let uu____84062 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____84064 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____84062 uu____84064
                                      else ());
                                     (let uu____84069 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _84084  -> FStar_Util.Inr _84084)
                                        uu____84069)))))
                 | ((s,t),(uu____84087,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____84090;
                                         FStar_Syntax_Syntax.vars =
                                           uu____84091;_}))
                     ->
                     let uu____84160 =
                       let uu____84162 = is_flex scrutinee  in
                       Prims.op_Negation uu____84162  in
                     if uu____84160
                     then
                       ((let uu____84173 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____84173
                         then
                           let uu____84178 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____84178
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____84197 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____84197
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____84212 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____84212
                           then
                             let uu____84217 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____84219 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____84217 uu____84219
                           else ());
                          (let pat_discriminates uu___613_84244 =
                             match uu___613_84244 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____84260;
                                  FStar_Syntax_Syntax.p = uu____84261;_},FStar_Pervasives_Native.None
                                ,uu____84262) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____84276;
                                  FStar_Syntax_Syntax.p = uu____84277;_},FStar_Pervasives_Native.None
                                ,uu____84278) -> true
                             | uu____84305 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____84408 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____84408 with
                                       | (uu____84410,uu____84411,t') ->
                                           let uu____84429 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____84429 with
                                            | (FullMatch ,uu____84441) ->
                                                true
                                            | (HeadMatch
                                               uu____84455,uu____84456) ->
                                                true
                                            | uu____84471 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____84508 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____84508
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____84519 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____84519 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____84607,uu____84608) ->
                                       branches1
                                   | uu____84753 -> branches  in
                                 let uu____84808 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____84817 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____84817 with
                                        | (p,uu____84821,uu____84822) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _84851  -> FStar_Util.Inr _84851)
                                   uu____84808))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____84881 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____84881 with
                                | (p,uu____84890,e) ->
                                    ((let uu____84909 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____84909
                                      then
                                        let uu____84914 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____84916 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____84914 uu____84916
                                      else ());
                                     (let uu____84921 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _84936  -> FStar_Util.Inr _84936)
                                        uu____84921)))))
                 | uu____84937 ->
                     ((let uu____84959 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____84959
                       then
                         let uu____84964 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____84966 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____84964 uu____84966
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____85012 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____85012
            then
              let uu____85017 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____85019 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____85021 = FStar_Syntax_Print.term_to_string t1  in
              let uu____85023 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____85017 uu____85019 uu____85021 uu____85023
            else ());
           (let uu____85028 = head_matches_delta env1 wl1 t1 t2  in
            match uu____85028 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____85059,uu____85060) ->
                     let rec may_relate head3 =
                       let uu____85088 =
                         let uu____85089 = FStar_Syntax_Subst.compress head3
                            in
                         uu____85089.FStar_Syntax_Syntax.n  in
                       match uu____85088 with
                       | FStar_Syntax_Syntax.Tm_name uu____85093 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____85095 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____85120 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____85120 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____85122 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____85125
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____85126 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____85129,uu____85130) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____85172) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____85178) ->
                           may_relate t
                       | uu____85183 -> false  in
                     let uu____85185 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____85185 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____85206 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____85206
                          then
                            let uu____85209 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____85209 with
                             | (guard,wl2) ->
                                 let uu____85216 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____85216)
                          else
                            (let uu____85219 =
                               let uu____85221 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____85223 =
                                 let uu____85225 =
                                   let uu____85229 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____85229
                                     (fun x  ->
                                        let uu____85236 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____85236)
                                    in
                                 FStar_Util.dflt "" uu____85225  in
                               let uu____85241 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____85243 =
                                 let uu____85245 =
                                   let uu____85249 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____85249
                                     (fun x  ->
                                        let uu____85256 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____85256)
                                    in
                                 FStar_Util.dflt "" uu____85245  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____85221 uu____85223 uu____85241
                                 uu____85243
                                in
                             giveup env1 uu____85219 orig))
                 | (HeadMatch (true ),uu____85262) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____85277 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____85277 with
                        | (guard,wl2) ->
                            let uu____85284 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____85284)
                     else
                       (let uu____85287 =
                          let uu____85289 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____85291 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____85289 uu____85291
                           in
                        giveup env1 uu____85287 orig)
                 | (uu____85294,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___3401_85308 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___3401_85308.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___3401_85308.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___3401_85308.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___3401_85308.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___3401_85308.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___3401_85308.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___3401_85308.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___3401_85308.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____85335 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____85335
          then
            let uu____85338 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____85338
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____85344 =
                let uu____85347 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____85347  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____85344 t1);
             (let uu____85366 =
                let uu____85369 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____85369  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____85366 t2);
             (let uu____85388 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____85388
              then
                let uu____85392 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____85394 =
                  let uu____85396 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____85398 =
                    let uu____85400 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____85400  in
                  Prims.op_Hat uu____85396 uu____85398  in
                let uu____85403 =
                  let uu____85405 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____85407 =
                    let uu____85409 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____85409  in
                  Prims.op_Hat uu____85405 uu____85407  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____85392 uu____85394 uu____85403
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____85416,uu____85417) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____85441,FStar_Syntax_Syntax.Tm_delayed uu____85442) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____85466,uu____85467) ->
                  let uu____85494 =
                    let uu___3432_85495 = problem  in
                    let uu____85496 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3432_85495.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____85496;
                      FStar_TypeChecker_Common.relation =
                        (uu___3432_85495.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3432_85495.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3432_85495.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3432_85495.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3432_85495.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3432_85495.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3432_85495.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3432_85495.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85494 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____85497,uu____85498) ->
                  let uu____85505 =
                    let uu___3438_85506 = problem  in
                    let uu____85507 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3438_85506.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____85507;
                      FStar_TypeChecker_Common.relation =
                        (uu___3438_85506.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3438_85506.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3438_85506.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3438_85506.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3438_85506.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3438_85506.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3438_85506.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3438_85506.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85505 wl
              | (uu____85508,FStar_Syntax_Syntax.Tm_ascribed uu____85509) ->
                  let uu____85536 =
                    let uu___3444_85537 = problem  in
                    let uu____85538 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3444_85537.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3444_85537.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3444_85537.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____85538;
                      FStar_TypeChecker_Common.element =
                        (uu___3444_85537.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3444_85537.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3444_85537.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3444_85537.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3444_85537.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3444_85537.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85536 wl
              | (uu____85539,FStar_Syntax_Syntax.Tm_meta uu____85540) ->
                  let uu____85547 =
                    let uu___3450_85548 = problem  in
                    let uu____85549 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3450_85548.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3450_85548.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3450_85548.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____85549;
                      FStar_TypeChecker_Common.element =
                        (uu___3450_85548.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3450_85548.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3450_85548.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3450_85548.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3450_85548.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3450_85548.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85547 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____85551),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____85553)) ->
                  let uu____85562 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____85562
              | (FStar_Syntax_Syntax.Tm_bvar uu____85563,uu____85564) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____85566,FStar_Syntax_Syntax.Tm_bvar uu____85567) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___614_85637 =
                    match uu___614_85637 with
                    | [] -> c
                    | bs ->
                        let uu____85665 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____85665
                     in
                  let uu____85676 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____85676 with
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
                                    let uu____85825 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____85825
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
                  let mk_t t l uu___615_85914 =
                    match uu___615_85914 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____85956 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____85956 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____86101 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____86102 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____86101
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____86102 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____86104,uu____86105) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____86136 -> true
                    | uu____86156 -> false  in
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
                      (let uu____86216 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_86224 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_86224.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_86224.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_86224.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_86224.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_86224.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_86224.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_86224.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_86224.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_86224.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_86224.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_86224.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_86224.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_86224.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_86224.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_86224.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_86224.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_86224.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_86224.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_86224.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_86224.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_86224.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_86224.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_86224.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_86224.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_86224.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_86224.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_86224.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_86224.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_86224.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_86224.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_86224.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_86224.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_86224.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_86224.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_86224.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_86224.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_86224.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_86224.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_86224.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_86224.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____86216 with
                       | (uu____86229,ty,uu____86231) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____86240 =
                                 let uu____86241 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____86241.FStar_Syntax_Syntax.n  in
                               match uu____86240 with
                               | FStar_Syntax_Syntax.Tm_refine uu____86244 ->
                                   let uu____86251 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____86251
                               | uu____86252 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____86255 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____86255
                             then
                               let uu____86260 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____86262 =
                                 let uu____86264 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____86264
                                  in
                               let uu____86265 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____86260 uu____86262 uu____86265
                             else ());
                            r1))
                     in
                  let uu____86270 =
                    let uu____86287 = maybe_eta t1  in
                    let uu____86294 = maybe_eta t2  in
                    (uu____86287, uu____86294)  in
                  (match uu____86270 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_86336 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_86336.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_86336.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_86336.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_86336.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_86336.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_86336.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_86336.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_86336.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____86357 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86357
                       then
                         let uu____86360 = destruct_flex_t not_abs wl  in
                         (match uu____86360 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86377 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86377.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86377.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86377.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86377.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86377.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86377.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86377.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86377.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____86401 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86401
                       then
                         let uu____86404 = destruct_flex_t not_abs wl  in
                         (match uu____86404 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86421 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86421.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86421.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86421.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86421.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86421.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86421.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86421.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86421.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____86425 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____86443,FStar_Syntax_Syntax.Tm_abs uu____86444) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____86475 -> true
                    | uu____86495 -> false  in
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
                      (let uu____86555 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_86563 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_86563.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_86563.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_86563.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_86563.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_86563.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_86563.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_86563.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_86563.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_86563.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_86563.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_86563.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_86563.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_86563.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_86563.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_86563.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_86563.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_86563.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_86563.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_86563.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_86563.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_86563.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_86563.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_86563.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_86563.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_86563.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_86563.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_86563.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_86563.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_86563.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_86563.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_86563.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_86563.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_86563.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_86563.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_86563.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_86563.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_86563.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_86563.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_86563.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_86563.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____86555 with
                       | (uu____86568,ty,uu____86570) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____86579 =
                                 let uu____86580 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____86580.FStar_Syntax_Syntax.n  in
                               match uu____86579 with
                               | FStar_Syntax_Syntax.Tm_refine uu____86583 ->
                                   let uu____86590 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____86590
                               | uu____86591 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____86594 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____86594
                             then
                               let uu____86599 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____86601 =
                                 let uu____86603 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____86603
                                  in
                               let uu____86604 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____86599 uu____86601 uu____86604
                             else ());
                            r1))
                     in
                  let uu____86609 =
                    let uu____86626 = maybe_eta t1  in
                    let uu____86633 = maybe_eta t2  in
                    (uu____86626, uu____86633)  in
                  (match uu____86609 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_86675 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_86675.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_86675.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_86675.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_86675.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_86675.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_86675.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_86675.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_86675.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____86696 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86696
                       then
                         let uu____86699 = destruct_flex_t not_abs wl  in
                         (match uu____86699 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86716 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86716.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86716.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86716.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86716.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86716.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86716.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86716.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86716.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____86740 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86740
                       then
                         let uu____86743 = destruct_flex_t not_abs wl  in
                         (match uu____86743 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86760 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86760.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86760.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86760.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86760.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86760.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86760.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86760.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86760.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____86764 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____86794 =
                    let uu____86799 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____86799 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3613_86827 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_86827.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_86827.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_86829 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_86829.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_86829.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____86830,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3613_86845 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_86845.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_86845.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_86847 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_86847.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_86847.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____86848 -> (x1, x2)  in
                  (match uu____86794 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____86867 = as_refinement false env t11  in
                       (match uu____86867 with
                        | (x12,phi11) ->
                            let uu____86875 = as_refinement false env t21  in
                            (match uu____86875 with
                             | (x22,phi21) ->
                                 ((let uu____86884 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____86884
                                   then
                                     ((let uu____86889 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____86891 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86893 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____86889
                                         uu____86891 uu____86893);
                                      (let uu____86896 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____86898 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86900 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____86896
                                         uu____86898 uu____86900))
                                   else ());
                                  (let uu____86905 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____86905 with
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
                                         let uu____86976 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____86976
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____86988 =
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
                                         (let uu____87001 =
                                            let uu____87004 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____87004
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____87001
                                            (p_guard base_prob));
                                         (let uu____87023 =
                                            let uu____87026 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____87026
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____87023
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____87045 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____87045)
                                          in
                                       let has_uvars =
                                         (let uu____87050 =
                                            let uu____87052 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____87052
                                             in
                                          Prims.op_Negation uu____87050) ||
                                           (let uu____87056 =
                                              let uu____87058 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____87058
                                               in
                                            Prims.op_Negation uu____87056)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____87062 =
                                           let uu____87067 =
                                             let uu____87076 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____87076]  in
                                           mk_t_problem wl1 uu____87067 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____87062 with
                                          | (ref_prob,wl2) ->
                                              let uu____87098 =
                                                solve env1
                                                  (let uu___3657_87100 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3657_87100.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3657_87100.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3657_87100.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3657_87100.tcenv);
                                                     wl_implicits =
                                                       (uu___3657_87100.wl_implicits)
                                                   })
                                                 in
                                              (match uu____87098 with
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
                                               | Success uu____87117 ->
                                                   let guard =
                                                     let uu____87125 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____87125
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3668_87134 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3668_87134.attempting);
                                                       wl_deferred =
                                                         (uu___3668_87134.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___3668_87134.defer_ok);
                                                       smt_ok =
                                                         (uu___3668_87134.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3668_87134.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3668_87134.tcenv);
                                                       wl_implicits =
                                                         (uu___3668_87134.wl_implicits)
                                                     }  in
                                                   let uu____87136 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____87136))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87139,FStar_Syntax_Syntax.Tm_uvar uu____87140) ->
                  let uu____87165 = destruct_flex_t t1 wl  in
                  (match uu____87165 with
                   | (f1,wl1) ->
                       let uu____87172 = destruct_flex_t t2 wl1  in
                       (match uu____87172 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87179;
                    FStar_Syntax_Syntax.pos = uu____87180;
                    FStar_Syntax_Syntax.vars = uu____87181;_},uu____87182),FStar_Syntax_Syntax.Tm_uvar
                 uu____87183) ->
                  let uu____87232 = destruct_flex_t t1 wl  in
                  (match uu____87232 with
                   | (f1,wl1) ->
                       let uu____87239 = destruct_flex_t t2 wl1  in
                       (match uu____87239 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87246,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87247;
                    FStar_Syntax_Syntax.pos = uu____87248;
                    FStar_Syntax_Syntax.vars = uu____87249;_},uu____87250))
                  ->
                  let uu____87299 = destruct_flex_t t1 wl  in
                  (match uu____87299 with
                   | (f1,wl1) ->
                       let uu____87306 = destruct_flex_t t2 wl1  in
                       (match uu____87306 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87313;
                    FStar_Syntax_Syntax.pos = uu____87314;
                    FStar_Syntax_Syntax.vars = uu____87315;_},uu____87316),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87317;
                    FStar_Syntax_Syntax.pos = uu____87318;
                    FStar_Syntax_Syntax.vars = uu____87319;_},uu____87320))
                  ->
                  let uu____87393 = destruct_flex_t t1 wl  in
                  (match uu____87393 with
                   | (f1,wl1) ->
                       let uu____87400 = destruct_flex_t t2 wl1  in
                       (match uu____87400 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____87407,uu____87408) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____87421 = destruct_flex_t t1 wl  in
                  (match uu____87421 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87428;
                    FStar_Syntax_Syntax.pos = uu____87429;
                    FStar_Syntax_Syntax.vars = uu____87430;_},uu____87431),uu____87432)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____87469 = destruct_flex_t t1 wl  in
                  (match uu____87469 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____87476,FStar_Syntax_Syntax.Tm_uvar uu____87477) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____87490,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87491;
                    FStar_Syntax_Syntax.pos = uu____87492;
                    FStar_Syntax_Syntax.vars = uu____87493;_},uu____87494))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87531,FStar_Syntax_Syntax.Tm_arrow uu____87532) ->
                  solve_t' env
                    (let uu___3768_87560 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_87560.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_87560.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_87560.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_87560.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_87560.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_87560.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_87560.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_87560.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_87560.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87561;
                    FStar_Syntax_Syntax.pos = uu____87562;
                    FStar_Syntax_Syntax.vars = uu____87563;_},uu____87564),FStar_Syntax_Syntax.Tm_arrow
                 uu____87565) ->
                  solve_t' env
                    (let uu___3768_87617 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_87617.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_87617.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_87617.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_87617.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_87617.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_87617.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_87617.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_87617.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_87617.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____87618,FStar_Syntax_Syntax.Tm_uvar uu____87619) ->
                  let uu____87632 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87632
              | (uu____87633,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87634;
                    FStar_Syntax_Syntax.pos = uu____87635;
                    FStar_Syntax_Syntax.vars = uu____87636;_},uu____87637))
                  ->
                  let uu____87674 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87674
              | (FStar_Syntax_Syntax.Tm_uvar uu____87675,uu____87676) ->
                  let uu____87689 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87689
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87690;
                    FStar_Syntax_Syntax.pos = uu____87691;
                    FStar_Syntax_Syntax.vars = uu____87692;_},uu____87693),uu____87694)
                  ->
                  let uu____87731 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87731
              | (FStar_Syntax_Syntax.Tm_refine uu____87732,uu____87733) ->
                  let t21 =
                    let uu____87741 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____87741  in
                  solve_t env
                    (let uu___3803_87767 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3803_87767.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3803_87767.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3803_87767.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3803_87767.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3803_87767.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3803_87767.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3803_87767.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3803_87767.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3803_87767.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____87768,FStar_Syntax_Syntax.Tm_refine uu____87769) ->
                  let t11 =
                    let uu____87777 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____87777  in
                  solve_t env
                    (let uu___3810_87803 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3810_87803.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3810_87803.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3810_87803.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3810_87803.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3810_87803.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3810_87803.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3810_87803.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3810_87803.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3810_87803.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____87885 =
                    let uu____87886 = guard_of_prob env wl problem t1 t2  in
                    match uu____87886 with
                    | (guard,wl1) ->
                        let uu____87893 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____87893
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____88112 = br1  in
                        (match uu____88112 with
                         | (p1,w1,uu____88141) ->
                             let uu____88158 = br2  in
                             (match uu____88158 with
                              | (p2,w2,uu____88181) ->
                                  let uu____88186 =
                                    let uu____88188 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____88188  in
                                  if uu____88186
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____88215 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____88215 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____88252 = br2  in
                                         (match uu____88252 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____88285 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____88285
                                                 in
                                              let uu____88290 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____88321,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____88342) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____88401 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____88401 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____88290
                                                (fun uu____88473  ->
                                                   match uu____88473 with
                                                   | (wprobs,wl2) ->
                                                       let uu____88510 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____88510
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____88531
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____88531
                                                              then
                                                                let uu____88536
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____88538
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____88536
                                                                  uu____88538
                                                              else ());
                                                             (let uu____88544
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____88544
                                                                (fun
                                                                   uu____88580
                                                                    ->
                                                                   match uu____88580
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
                    | uu____88709 -> FStar_Pervasives_Native.None  in
                  let uu____88750 = solve_branches wl brs1 brs2  in
                  (match uu____88750 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____88801 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____88801 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____88835 =
                                FStar_List.map
                                  (fun uu____88847  ->
                                     match uu____88847 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____88835  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____88856 =
                              let uu____88857 =
                                let uu____88858 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____88858
                                  (let uu___3909_88866 = wl3  in
                                   {
                                     attempting =
                                       (uu___3909_88866.attempting);
                                     wl_deferred =
                                       (uu___3909_88866.wl_deferred);
                                     ctr = (uu___3909_88866.ctr);
                                     defer_ok = (uu___3909_88866.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3909_88866.umax_heuristic_ok);
                                     tcenv = (uu___3909_88866.tcenv);
                                     wl_implicits =
                                       (uu___3909_88866.wl_implicits)
                                   })
                                 in
                              solve env uu____88857  in
                            (match uu____88856 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____88871 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____88878,uu____88879) ->
                  let head1 =
                    let uu____88903 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____88903
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____88949 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____88949
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____88995 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____88995
                    then
                      let uu____88999 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89001 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89003 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____88999 uu____89001 uu____89003
                    else ());
                   (let no_free_uvars t =
                      (let uu____89017 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89017) &&
                        (let uu____89021 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89021)
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
                      let uu____89038 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89038 = FStar_Syntax_Util.Equal  in
                    let uu____89039 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89039
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89043 = equal t1 t2  in
                         (if uu____89043
                          then
                            let uu____89046 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89046
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89051 =
                            let uu____89058 = equal t1 t2  in
                            if uu____89058
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89071 = mk_eq2 wl env orig t1 t2  in
                               match uu____89071 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89051 with
                          | (guard,wl1) ->
                              let uu____89092 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89092))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____89095,uu____89096) ->
                  let head1 =
                    let uu____89104 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89104
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89150 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89150
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89196 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89196
                    then
                      let uu____89200 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89202 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89204 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89200 uu____89202 uu____89204
                    else ());
                   (let no_free_uvars t =
                      (let uu____89218 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89218) &&
                        (let uu____89222 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89222)
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
                      let uu____89239 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89239 = FStar_Syntax_Util.Equal  in
                    let uu____89240 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89240
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89244 = equal t1 t2  in
                         (if uu____89244
                          then
                            let uu____89247 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89247
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89252 =
                            let uu____89259 = equal t1 t2  in
                            if uu____89259
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89272 = mk_eq2 wl env orig t1 t2  in
                               match uu____89272 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89252 with
                          | (guard,wl1) ->
                              let uu____89293 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89293))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____89296,uu____89297) ->
                  let head1 =
                    let uu____89299 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89299
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89345 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89345
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89391 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89391
                    then
                      let uu____89395 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89397 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89399 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89395 uu____89397 uu____89399
                    else ());
                   (let no_free_uvars t =
                      (let uu____89413 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89413) &&
                        (let uu____89417 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89417)
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
                      let uu____89434 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89434 = FStar_Syntax_Util.Equal  in
                    let uu____89435 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89435
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89439 = equal t1 t2  in
                         (if uu____89439
                          then
                            let uu____89442 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89442
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89447 =
                            let uu____89454 = equal t1 t2  in
                            if uu____89454
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89467 = mk_eq2 wl env orig t1 t2  in
                               match uu____89467 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89447 with
                          | (guard,wl1) ->
                              let uu____89488 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89488))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____89491,uu____89492) ->
                  let head1 =
                    let uu____89494 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89494
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89540 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89540
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89586 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89586
                    then
                      let uu____89590 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89592 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89594 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89590 uu____89592 uu____89594
                    else ());
                   (let no_free_uvars t =
                      (let uu____89608 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89608) &&
                        (let uu____89612 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89612)
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
                      let uu____89629 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89629 = FStar_Syntax_Util.Equal  in
                    let uu____89630 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89630
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89634 = equal t1 t2  in
                         (if uu____89634
                          then
                            let uu____89637 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89637
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89642 =
                            let uu____89649 = equal t1 t2  in
                            if uu____89649
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89662 = mk_eq2 wl env orig t1 t2  in
                               match uu____89662 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89642 with
                          | (guard,wl1) ->
                              let uu____89683 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89683))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____89686,uu____89687) ->
                  let head1 =
                    let uu____89689 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89689
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89735 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89735
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89781 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89781
                    then
                      let uu____89785 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89787 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89789 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89785 uu____89787 uu____89789
                    else ());
                   (let no_free_uvars t =
                      (let uu____89803 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89803) &&
                        (let uu____89807 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89807)
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
                      let uu____89824 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89824 = FStar_Syntax_Util.Equal  in
                    let uu____89825 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89825
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89829 = equal t1 t2  in
                         (if uu____89829
                          then
                            let uu____89832 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89832
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89837 =
                            let uu____89844 = equal t1 t2  in
                            if uu____89844
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89857 = mk_eq2 wl env orig t1 t2  in
                               match uu____89857 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89837 with
                          | (guard,wl1) ->
                              let uu____89878 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89878))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____89881,uu____89882) ->
                  let head1 =
                    let uu____89900 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89900
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89946 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89946
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89992 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89992
                    then
                      let uu____89996 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89998 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90000 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89996 uu____89998 uu____90000
                    else ());
                   (let no_free_uvars t =
                      (let uu____90014 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90014) &&
                        (let uu____90018 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90018)
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
                      let uu____90035 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90035 = FStar_Syntax_Util.Equal  in
                    let uu____90036 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90036
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90040 = equal t1 t2  in
                         (if uu____90040
                          then
                            let uu____90043 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90043
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90048 =
                            let uu____90055 = equal t1 t2  in
                            if uu____90055
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90068 = mk_eq2 wl env orig t1 t2  in
                               match uu____90068 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90048 with
                          | (guard,wl1) ->
                              let uu____90089 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90089))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90092,FStar_Syntax_Syntax.Tm_match uu____90093) ->
                  let head1 =
                    let uu____90117 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90117
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90163 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90163
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90209 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90209
                    then
                      let uu____90213 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90215 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90217 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90213 uu____90215 uu____90217
                    else ());
                   (let no_free_uvars t =
                      (let uu____90231 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90231) &&
                        (let uu____90235 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90235)
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
                      let uu____90252 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90252 = FStar_Syntax_Util.Equal  in
                    let uu____90253 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90253
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90257 = equal t1 t2  in
                         (if uu____90257
                          then
                            let uu____90260 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90260
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90265 =
                            let uu____90272 = equal t1 t2  in
                            if uu____90272
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90285 = mk_eq2 wl env orig t1 t2  in
                               match uu____90285 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90265 with
                          | (guard,wl1) ->
                              let uu____90306 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90306))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90309,FStar_Syntax_Syntax.Tm_uinst uu____90310) ->
                  let head1 =
                    let uu____90318 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90318
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90358 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90358
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90398 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90398
                    then
                      let uu____90402 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90404 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90406 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90402 uu____90404 uu____90406
                    else ());
                   (let no_free_uvars t =
                      (let uu____90420 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90420) &&
                        (let uu____90424 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90424)
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
                      let uu____90441 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90441 = FStar_Syntax_Util.Equal  in
                    let uu____90442 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90442
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90446 = equal t1 t2  in
                         (if uu____90446
                          then
                            let uu____90449 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90449
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90454 =
                            let uu____90461 = equal t1 t2  in
                            if uu____90461
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90474 = mk_eq2 wl env orig t1 t2  in
                               match uu____90474 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90454 with
                          | (guard,wl1) ->
                              let uu____90495 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90495))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90498,FStar_Syntax_Syntax.Tm_name uu____90499) ->
                  let head1 =
                    let uu____90501 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90501
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90541 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90541
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90581 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90581
                    then
                      let uu____90585 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90587 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90589 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90585 uu____90587 uu____90589
                    else ());
                   (let no_free_uvars t =
                      (let uu____90603 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90603) &&
                        (let uu____90607 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90607)
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
                      let uu____90624 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90624 = FStar_Syntax_Util.Equal  in
                    let uu____90625 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90625
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90629 = equal t1 t2  in
                         (if uu____90629
                          then
                            let uu____90632 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90632
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90637 =
                            let uu____90644 = equal t1 t2  in
                            if uu____90644
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90657 = mk_eq2 wl env orig t1 t2  in
                               match uu____90657 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90637 with
                          | (guard,wl1) ->
                              let uu____90678 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90678))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90681,FStar_Syntax_Syntax.Tm_constant uu____90682) ->
                  let head1 =
                    let uu____90684 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90684
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90724 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90724
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90764 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90764
                    then
                      let uu____90768 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90770 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90772 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90768 uu____90770 uu____90772
                    else ());
                   (let no_free_uvars t =
                      (let uu____90786 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90786) &&
                        (let uu____90790 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90790)
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
                      let uu____90807 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90807 = FStar_Syntax_Util.Equal  in
                    let uu____90808 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90808
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90812 = equal t1 t2  in
                         (if uu____90812
                          then
                            let uu____90815 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90815
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90820 =
                            let uu____90827 = equal t1 t2  in
                            if uu____90827
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90840 = mk_eq2 wl env orig t1 t2  in
                               match uu____90840 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90820 with
                          | (guard,wl1) ->
                              let uu____90861 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90861))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90864,FStar_Syntax_Syntax.Tm_fvar uu____90865) ->
                  let head1 =
                    let uu____90867 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90867
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90907 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90907
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90947 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90947
                    then
                      let uu____90951 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90953 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90955 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90951 uu____90953 uu____90955
                    else ());
                   (let no_free_uvars t =
                      (let uu____90969 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90969) &&
                        (let uu____90973 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90973)
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
                      let uu____90990 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90990 = FStar_Syntax_Util.Equal  in
                    let uu____90991 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90991
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90995 = equal t1 t2  in
                         (if uu____90995
                          then
                            let uu____90998 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90998
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____91003 =
                            let uu____91010 = equal t1 t2  in
                            if uu____91010
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____91023 = mk_eq2 wl env orig t1 t2  in
                               match uu____91023 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____91003 with
                          | (guard,wl1) ->
                              let uu____91044 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____91044))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____91047,FStar_Syntax_Syntax.Tm_app uu____91048) ->
                  let head1 =
                    let uu____91066 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____91066
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____91106 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____91106
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____91146 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____91146
                    then
                      let uu____91150 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____91152 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____91154 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____91150 uu____91152 uu____91154
                    else ());
                   (let no_free_uvars t =
                      (let uu____91168 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____91168) &&
                        (let uu____91172 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____91172)
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
                      let uu____91189 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____91189 = FStar_Syntax_Util.Equal  in
                    let uu____91190 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____91190
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____91194 = equal t1 t2  in
                         (if uu____91194
                          then
                            let uu____91197 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____91197
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____91202 =
                            let uu____91209 = equal t1 t2  in
                            if uu____91209
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____91222 = mk_eq2 wl env orig t1 t2  in
                               match uu____91222 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____91202 with
                          | (guard,wl1) ->
                              let uu____91243 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____91243))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____91246,FStar_Syntax_Syntax.Tm_let uu____91247) ->
                  let uu____91274 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____91274
                  then
                    let uu____91277 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____91277
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____91281,uu____91282) ->
                  let uu____91296 =
                    let uu____91302 =
                      let uu____91304 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____91306 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____91308 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____91310 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____91304 uu____91306 uu____91308 uu____91310
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____91302)
                     in
                  FStar_Errors.raise_error uu____91296
                    t1.FStar_Syntax_Syntax.pos
              | (uu____91314,FStar_Syntax_Syntax.Tm_let uu____91315) ->
                  let uu____91329 =
                    let uu____91335 =
                      let uu____91337 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____91339 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____91341 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____91343 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____91337 uu____91339 uu____91341 uu____91343
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____91335)
                     in
                  FStar_Errors.raise_error uu____91329
                    t1.FStar_Syntax_Syntax.pos
              | uu____91347 -> giveup env "head tag mismatch" orig))))

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
          (let uu____91411 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____91411
           then
             let uu____91416 =
               let uu____91418 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____91418  in
             let uu____91419 =
               let uu____91421 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____91421  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____91416 uu____91419
           else ());
          (let uu____91425 =
             let uu____91427 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____91427  in
           if uu____91425
           then
             let uu____91430 =
               let uu____91432 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____91434 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____91432 uu____91434
                in
             giveup env uu____91430 orig
           else
             (let uu____91439 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____91439 with
              | (ret_sub_prob,wl1) ->
                  let uu____91447 =
                    FStar_List.fold_right2
                      (fun uu____91484  ->
                         fun uu____91485  ->
                           fun uu____91486  ->
                             match (uu____91484, uu____91485, uu____91486)
                             with
                             | ((a1,uu____91530),(a2,uu____91532),(arg_sub_probs,wl2))
                                 ->
                                 let uu____91565 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____91565 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____91447 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____91595 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____91595  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____91603 = attempt sub_probs wl3  in
                       solve env uu____91603)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____91626 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____91629)::[] -> wp1
              | uu____91654 ->
                  let uu____91665 =
                    let uu____91667 =
                      let uu____91669 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____91669  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____91667
                     in
                  failwith uu____91665
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____91676 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____91676]
              | x -> x  in
            let uu____91678 =
              let uu____91689 =
                let uu____91698 =
                  let uu____91699 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____91699 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____91698  in
              [uu____91689]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____91678;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____91717 = lift_c1 ()  in solve_eq uu____91717 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___616_91726  ->
                       match uu___616_91726 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____91731 -> false))
                in
             let uu____91733 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____91763)::uu____91764,(wp2,uu____91766)::uu____91767)
                   -> (wp1, wp2)
               | uu____91840 ->
                   let uu____91865 =
                     let uu____91871 =
                       let uu____91873 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____91875 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____91873 uu____91875
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____91871)
                      in
                   FStar_Errors.raise_error uu____91865
                     env.FStar_TypeChecker_Env.range
                in
             match uu____91733 with
             | (wpc1,wpc2) ->
                 let uu____91885 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____91885
                 then
                   let uu____91890 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____91890 wl
                 else
                   (let uu____91894 =
                      let uu____91901 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____91901  in
                    match uu____91894 with
                    | (c2_decl,qualifiers) ->
                        let uu____91922 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____91922
                        then
                          let c1_repr =
                            let uu____91929 =
                              let uu____91930 =
                                let uu____91931 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____91931  in
                              let uu____91932 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____91930 uu____91932
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____91929
                             in
                          let c2_repr =
                            let uu____91934 =
                              let uu____91935 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____91936 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____91935 uu____91936
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____91934
                             in
                          let uu____91937 =
                            let uu____91942 =
                              let uu____91944 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____91946 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____91944 uu____91946
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____91942
                             in
                          (match uu____91937 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____91952 = attempt [prob] wl2  in
                               solve env uu____91952)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____91967 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____91967
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____91976 =
                                     let uu____91983 =
                                       let uu____91984 =
                                         let uu____92001 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____92004 =
                                           let uu____92015 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____92024 =
                                             let uu____92035 =
                                               let uu____92044 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____92044
                                                in
                                             [uu____92035]  in
                                           uu____92015 :: uu____92024  in
                                         (uu____92001, uu____92004)  in
                                       FStar_Syntax_Syntax.Tm_app uu____91984
                                        in
                                     FStar_Syntax_Syntax.mk uu____91983  in
                                   uu____91976 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____92096 =
                                    let uu____92103 =
                                      let uu____92104 =
                                        let uu____92121 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____92124 =
                                          let uu____92135 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____92144 =
                                            let uu____92155 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____92164 =
                                              let uu____92175 =
                                                let uu____92184 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____92184
                                                 in
                                              [uu____92175]  in
                                            uu____92155 :: uu____92164  in
                                          uu____92135 :: uu____92144  in
                                        (uu____92121, uu____92124)  in
                                      FStar_Syntax_Syntax.Tm_app uu____92104
                                       in
                                    FStar_Syntax_Syntax.mk uu____92103  in
                                  uu____92096 FStar_Pervasives_Native.None r)
                              in
                           (let uu____92241 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____92241
                            then
                              let uu____92246 =
                                let uu____92248 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____92248
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____92246
                            else ());
                           (let uu____92252 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____92252 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____92261 =
                                    let uu____92264 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _92267  ->
                                         FStar_Pervasives_Native.Some _92267)
                                      uu____92264
                                     in
                                  solve_prob orig uu____92261 [] wl1  in
                                let uu____92268 = attempt [base_prob] wl2  in
                                solve env uu____92268))))
           in
        let uu____92269 = FStar_Util.physical_equality c1 c2  in
        if uu____92269
        then
          let uu____92272 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____92272
        else
          ((let uu____92276 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____92276
            then
              let uu____92281 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____92283 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____92281
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____92283
            else ());
           (let uu____92288 =
              let uu____92297 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____92300 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____92297, uu____92300)  in
            match uu____92288 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____92318),FStar_Syntax_Syntax.Total
                    (t2,uu____92320)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____92337 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92337 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____92339,FStar_Syntax_Syntax.Total uu____92340) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____92359),FStar_Syntax_Syntax.Total
                    (t2,uu____92361)) ->
                     let uu____92378 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92378 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____92381),FStar_Syntax_Syntax.GTotal
                    (t2,uu____92383)) ->
                     let uu____92400 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92400 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____92403),FStar_Syntax_Syntax.GTotal
                    (t2,uu____92405)) ->
                     let uu____92422 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92422 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____92424,FStar_Syntax_Syntax.Comp uu____92425) ->
                     let uu____92434 =
                       let uu___4158_92437 = problem  in
                       let uu____92440 =
                         let uu____92441 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92441
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_92437.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____92440;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_92437.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_92437.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_92437.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_92437.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_92437.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_92437.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_92437.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_92437.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92434 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____92442,FStar_Syntax_Syntax.Comp uu____92443) ->
                     let uu____92452 =
                       let uu___4158_92455 = problem  in
                       let uu____92458 =
                         let uu____92459 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92459
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_92455.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____92458;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_92455.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_92455.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_92455.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_92455.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_92455.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_92455.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_92455.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_92455.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92452 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92460,FStar_Syntax_Syntax.GTotal uu____92461) ->
                     let uu____92470 =
                       let uu___4170_92473 = problem  in
                       let uu____92476 =
                         let uu____92477 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92477
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_92473.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_92473.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_92473.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____92476;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_92473.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_92473.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_92473.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_92473.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_92473.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_92473.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92470 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92478,FStar_Syntax_Syntax.Total uu____92479) ->
                     let uu____92488 =
                       let uu___4170_92491 = problem  in
                       let uu____92494 =
                         let uu____92495 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92495
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_92491.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_92491.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_92491.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____92494;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_92491.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_92491.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_92491.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_92491.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_92491.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_92491.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92488 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92496,FStar_Syntax_Syntax.Comp uu____92497) ->
                     let uu____92498 =
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
                     if uu____92498
                     then
                       let uu____92501 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____92501 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____92508 =
                            let uu____92513 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____92513
                            then (c1_comp, c2_comp)
                            else
                              (let uu____92522 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____92523 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____92522, uu____92523))
                             in
                          match uu____92508 with
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
                           (let uu____92531 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____92531
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____92539 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____92539 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____92542 =
                                  let uu____92544 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____92546 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____92544 uu____92546
                                   in
                                giveup env uu____92542 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____92557 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____92557 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____92607 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____92607 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____92632 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____92663  ->
                match uu____92663 with
                | (u1,u2) ->
                    let uu____92671 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____92673 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____92671 uu____92673))
         in
      FStar_All.pipe_right uu____92632 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____92710,[])) when
          let uu____92737 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____92737 -> "{}"
      | uu____92740 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____92767 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____92767
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____92779 =
              FStar_List.map
                (fun uu____92792  ->
                   match uu____92792 with
                   | (uu____92799,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____92779 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____92810 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____92810 imps
  
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
                  let uu____92867 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____92867
                  then
                    let uu____92875 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____92877 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____92875
                      (rel_to_string rel) uu____92877
                  else "TOP"  in
                let uu____92883 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____92883 with
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
              let uu____92943 =
                let uu____92946 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _92949  -> FStar_Pervasives_Native.Some _92949)
                  uu____92946
                 in
              FStar_Syntax_Syntax.new_bv uu____92943 t1  in
            let uu____92950 =
              let uu____92955 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____92955
               in
            match uu____92950 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____93015 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____93015
         then
           let uu____93020 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____93020
         else ());
        (let uu____93027 =
           FStar_Util.record_time (fun uu____93034  -> solve env probs)  in
         match uu____93027 with
         | (sol,ms) ->
             ((let uu____93046 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____93046
               then
                 let uu____93051 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____93051
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____93064 =
                     FStar_Util.record_time
                       (fun uu____93071  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____93064 with
                    | ((),ms1) ->
                        ((let uu____93082 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____93082
                          then
                            let uu____93087 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____93087
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____93101 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____93101
                     then
                       let uu____93108 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____93108
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
          ((let uu____93135 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____93135
            then
              let uu____93140 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____93140
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____93147 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____93147
             then
               let uu____93152 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____93152
             else ());
            (let f2 =
               let uu____93158 =
                 let uu____93159 = FStar_Syntax_Util.unmeta f1  in
                 uu____93159.FStar_Syntax_Syntax.n  in
               match uu____93158 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____93163 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4286_93164 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___4286_93164.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___4286_93164.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___4286_93164.FStar_TypeChecker_Env.implicits)
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
            let uu____93219 =
              let uu____93220 =
                let uu____93221 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _93222  ->
                       FStar_TypeChecker_Common.NonTrivial _93222)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____93221;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____93220  in
            FStar_All.pipe_left
              (fun _93229  -> FStar_Pervasives_Native.Some _93229)
              uu____93219
  
let with_guard_no_simp :
  'Auu____93239 .
    'Auu____93239 ->
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
            let uu____93262 =
              let uu____93263 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _93264  -> FStar_TypeChecker_Common.NonTrivial _93264)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____93263;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____93262
  
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
          (let uu____93297 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____93297
           then
             let uu____93302 = FStar_Syntax_Print.term_to_string t1  in
             let uu____93304 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____93302
               uu____93304
           else ());
          (let uu____93309 =
             let uu____93314 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____93314
              in
           match uu____93309 with
           | (prob,wl) ->
               let g =
                 let uu____93322 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____93332  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____93322  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____93368 = try_teq true env t1 t2  in
        match uu____93368 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____93373 = FStar_TypeChecker_Env.get_range env  in
              let uu____93374 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____93373 uu____93374);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____93382 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____93382
              then
                let uu____93387 = FStar_Syntax_Print.term_to_string t1  in
                let uu____93389 = FStar_Syntax_Print.term_to_string t2  in
                let uu____93391 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____93387
                  uu____93389 uu____93391
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
          let uu____93417 = FStar_TypeChecker_Env.get_range env  in
          let uu____93418 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____93417 uu____93418
  
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
        (let uu____93447 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____93447
         then
           let uu____93452 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____93454 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____93452 uu____93454
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____93465 =
           let uu____93472 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____93472 "sub_comp"
            in
         match uu____93465 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____93485 =
                 FStar_Util.record_time
                   (fun uu____93497  ->
                      let uu____93498 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____93509  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____93498)
                  in
               match uu____93485 with
               | (r,ms) ->
                   ((let uu____93540 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____93540
                     then
                       let uu____93545 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____93547 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____93549 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____93545 uu____93547
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____93549
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
      fun uu____93587  ->
        match uu____93587 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____93630 =
                 let uu____93636 =
                   let uu____93638 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____93640 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____93638 uu____93640
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____93636)  in
               let uu____93644 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____93630 uu____93644)
               in
            let equiv1 v1 v' =
              let uu____93657 =
                let uu____93662 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____93663 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____93662, uu____93663)  in
              match uu____93657 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____93683 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____93714 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____93714 with
                      | FStar_Syntax_Syntax.U_unif uu____93721 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____93750  ->
                                    match uu____93750 with
                                    | (u,v') ->
                                        let uu____93759 = equiv1 v1 v'  in
                                        if uu____93759
                                        then
                                          let uu____93764 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____93764 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____93785 -> []))
               in
            let uu____93790 =
              let wl =
                let uu___4377_93794 = empty_worklist env  in
                {
                  attempting = (uu___4377_93794.attempting);
                  wl_deferred = (uu___4377_93794.wl_deferred);
                  ctr = (uu___4377_93794.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4377_93794.smt_ok);
                  umax_heuristic_ok = (uu___4377_93794.umax_heuristic_ok);
                  tcenv = (uu___4377_93794.tcenv);
                  wl_implicits = (uu___4377_93794.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____93813  ->
                      match uu____93813 with
                      | (lb,v1) ->
                          let uu____93820 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____93820 with
                           | USolved wl1 -> ()
                           | uu____93823 -> fail1 lb v1)))
               in
            let rec check_ineq uu____93834 =
              match uu____93834 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____93846) -> true
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
                      uu____93870,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____93872,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____93883) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____93891,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____93900 -> false)
               in
            let uu____93906 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____93923  ->
                      match uu____93923 with
                      | (u,v1) ->
                          let uu____93931 = check_ineq (u, v1)  in
                          if uu____93931
                          then true
                          else
                            ((let uu____93939 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____93939
                              then
                                let uu____93944 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____93946 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____93944
                                  uu____93946
                              else ());
                             false)))
               in
            if uu____93906
            then ()
            else
              ((let uu____93956 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____93956
                then
                  ((let uu____93962 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____93962);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____93974 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____93974))
                else ());
               (let uu____93987 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____93987))
  
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
        let fail1 uu____94061 =
          match uu____94061 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4454_94087 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___4454_94087.attempting);
            wl_deferred = (uu___4454_94087.wl_deferred);
            ctr = (uu___4454_94087.ctr);
            defer_ok;
            smt_ok = (uu___4454_94087.smt_ok);
            umax_heuristic_ok = (uu___4454_94087.umax_heuristic_ok);
            tcenv = (uu___4454_94087.tcenv);
            wl_implicits = (uu___4454_94087.wl_implicits)
          }  in
        (let uu____94090 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____94090
         then
           let uu____94095 = FStar_Util.string_of_bool defer_ok  in
           let uu____94097 = wl_to_string wl  in
           let uu____94099 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____94095 uu____94097 uu____94099
         else ());
        (let g1 =
           let uu____94105 = solve_and_commit env wl fail1  in
           match uu____94105 with
           | FStar_Pervasives_Native.Some
               (uu____94112::uu____94113,uu____94114) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4469_94143 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___4469_94143.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___4469_94143.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____94144 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___4474_94153 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4474_94153.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4474_94153.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___4474_94153.FStar_TypeChecker_Env.implicits)
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
    let uu____94207 = FStar_ST.op_Bang last_proof_ns  in
    match uu____94207 with
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
            let uu___4493_94332 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___4493_94332.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___4493_94332.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___4493_94332.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____94333 =
            let uu____94335 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____94335  in
          if uu____94333
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____94347 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____94348 =
                       let uu____94350 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____94350
                        in
                     FStar_Errors.diag uu____94347 uu____94348)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____94358 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____94359 =
                        let uu____94361 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____94361
                         in
                      FStar_Errors.diag uu____94358 uu____94359)
                   else ();
                   (let uu____94367 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____94367
                      "discharge_guard'" env vc1);
                   (let uu____94369 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____94369 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____94378 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____94379 =
                                let uu____94381 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____94381
                                 in
                              FStar_Errors.diag uu____94378 uu____94379)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____94391 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____94392 =
                                let uu____94394 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____94394
                                 in
                              FStar_Errors.diag uu____94391 uu____94392)
                           else ();
                           (let vcs =
                              let uu____94408 = FStar_Options.use_tactics ()
                                 in
                              if uu____94408
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____94430  ->
                                     (let uu____94432 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____94432);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____94476  ->
                                              match uu____94476 with
                                              | (env1,goal,opts) ->
                                                  let uu____94492 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____94492, opts)))))
                              else
                                (let uu____94495 =
                                   let uu____94502 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____94502)  in
                                 [uu____94495])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____94535  ->
                                    match uu____94535 with
                                    | (env1,goal,opts) ->
                                        let uu____94545 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____94545 with
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
                                                (let uu____94557 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____94558 =
                                                   let uu____94560 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____94562 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____94560 uu____94562
                                                    in
                                                 FStar_Errors.diag
                                                   uu____94557 uu____94558)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____94569 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____94570 =
                                                   let uu____94572 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____94572
                                                    in
                                                 FStar_Errors.diag
                                                   uu____94569 uu____94570)
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
      let uu____94590 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____94590 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____94599 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____94599
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____94613 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____94613 with
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
        let uu____94643 = try_teq false env t1 t2  in
        match uu____94643 with
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
            let uu____94687 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____94687 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____94700 ->
                     let uu____94713 =
                       let uu____94714 = FStar_Syntax_Subst.compress r  in
                       uu____94714.FStar_Syntax_Syntax.n  in
                     (match uu____94713 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____94719) ->
                          unresolved ctx_u'
                      | uu____94736 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____94760 = acc  in
            match uu____94760 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____94779 = hd1  in
                     (match uu____94779 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____94790 = unresolved ctx_u  in
                             if uu____94790
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____94814 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____94814
                                     then
                                       let uu____94818 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____94818
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____94827 = teq_nosmt env1 t tm
                                          in
                                       match uu____94827 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4606_94837 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4606_94837.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4606_94837.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4606_94837.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4606_94837.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4606_94837.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4606_94837.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4606_94837.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4609_94845 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4609_94845.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4609_94845.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4609_94845.FStar_TypeChecker_Env.imp_range)
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
                                    let uu___4613_94856 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4613_94856.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4613_94856.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4613_94856.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4613_94856.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4613_94856.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4613_94856.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4613_94856.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4613_94856.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4613_94856.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4613_94856.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4613_94856.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4613_94856.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4613_94856.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4613_94856.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4613_94856.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4613_94856.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4613_94856.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4613_94856.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4613_94856.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4613_94856.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4613_94856.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4613_94856.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4613_94856.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4613_94856.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4613_94856.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4613_94856.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4613_94856.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4613_94856.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4613_94856.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4613_94856.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4613_94856.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4613_94856.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4613_94856.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4613_94856.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4613_94856.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4613_94856.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4613_94856.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4613_94856.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4613_94856.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4613_94856.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4613_94856.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4613_94856.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4618_94860 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4618_94860.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4618_94860.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4618_94860.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4618_94860.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4618_94860.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4618_94860.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4618_94860.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4618_94860.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4618_94860.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4618_94860.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4618_94860.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4618_94860.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4618_94860.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4618_94860.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4618_94860.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4618_94860.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4618_94860.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4618_94860.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4618_94860.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4618_94860.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4618_94860.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4618_94860.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4618_94860.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4618_94860.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4618_94860.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4618_94860.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4618_94860.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4618_94860.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4618_94860.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4618_94860.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4618_94860.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4618_94860.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4618_94860.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4618_94860.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4618_94860.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4618_94860.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4618_94860.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4618_94860.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4618_94860.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4618_94860.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4618_94860.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4618_94860.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____94865 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____94865
                                   then
                                     let uu____94870 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____94872 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____94874 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____94876 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____94870 uu____94872 uu____94874
                                       reason uu____94876
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4624_94883  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____94890 =
                                             let uu____94900 =
                                               let uu____94908 =
                                                 let uu____94910 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____94912 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____94914 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____94910 uu____94912
                                                   uu____94914
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____94908, r)
                                                in
                                             [uu____94900]  in
                                           FStar_Errors.add_errors
                                             uu____94890);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4632_94934 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4632_94934.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4632_94934.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4632_94934.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____94938 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____94949  ->
                                               let uu____94950 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____94952 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____94954 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____94950 uu____94952
                                                 reason uu____94954)) env2 g2
                                         true
                                        in
                                     match uu____94938 with
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
          let uu___4640_94962 = g  in
          let uu____94963 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4640_94962.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4640_94962.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4640_94962.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____94963
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
        let uu____95006 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____95006 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____95007 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____95007
      | imp::uu____95009 ->
          let uu____95012 =
            let uu____95018 =
              let uu____95020 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____95022 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____95020 uu____95022 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____95018)
             in
          FStar_Errors.raise_error uu____95012
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95044 = teq_nosmt env t1 t2  in
        match uu____95044 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4662_95063 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4662_95063.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4662_95063.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4662_95063.FStar_TypeChecker_Env.implicits)
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
        (let uu____95099 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____95099
         then
           let uu____95104 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____95106 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____95104
             uu____95106
         else ());
        (let uu____95111 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____95111 with
         | (prob,x,wl) ->
             let g =
               let uu____95130 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____95141  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____95130  in
             ((let uu____95162 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____95162
               then
                 let uu____95167 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____95169 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____95171 =
                   let uu____95173 = FStar_Util.must g  in
                   guard_to_string env uu____95173  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____95167 uu____95169 uu____95171
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
        let uu____95210 = check_subtyping env t1 t2  in
        match uu____95210 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____95229 =
              let uu____95230 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____95230 g  in
            FStar_Pervasives_Native.Some uu____95229
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95249 = check_subtyping env t1 t2  in
        match uu____95249 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____95268 =
              let uu____95269 =
                let uu____95270 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____95270]  in
              FStar_TypeChecker_Env.close_guard env uu____95269 g  in
            FStar_Pervasives_Native.Some uu____95268
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____95308 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____95308
         then
           let uu____95313 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____95315 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____95313
             uu____95315
         else ());
        (let uu____95320 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____95320 with
         | (prob,x,wl) ->
             let g =
               let uu____95335 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____95346  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____95335  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____95370 =
                      let uu____95371 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____95371]  in
                    FStar_TypeChecker_Env.close_guard env uu____95370 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95412 = subtype_nosmt env t1 t2  in
        match uu____95412 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  