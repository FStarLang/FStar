open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____65053 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____65089 -> false
  
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
                    let uu____65513 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____65513;
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
                     (let uu___656_65545 = wl  in
                      {
                        attempting = (uu___656_65545.attempting);
                        wl_deferred = (uu___656_65545.wl_deferred);
                        ctr = (uu___656_65545.ctr);
                        defer_ok = (uu___656_65545.defer_ok);
                        smt_ok = (uu___656_65545.smt_ok);
                        umax_heuristic_ok =
                          (uu___656_65545.umax_heuristic_ok);
                        tcenv = (uu___656_65545.tcenv);
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
            let uu___662_65578 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___662_65578.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___662_65578.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___662_65578.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___662_65578.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___662_65578.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___662_65578.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___662_65578.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___662_65578.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___662_65578.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___662_65578.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___662_65578.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___662_65578.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___662_65578.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___662_65578.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___662_65578.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___662_65578.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___662_65578.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___662_65578.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___662_65578.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___662_65578.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___662_65578.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___662_65578.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___662_65578.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___662_65578.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___662_65578.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___662_65578.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___662_65578.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___662_65578.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___662_65578.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___662_65578.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___662_65578.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___662_65578.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___662_65578.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___662_65578.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___662_65578.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___662_65578.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___662_65578.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___662_65578.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___662_65578.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___662_65578.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___662_65578.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___662_65578.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____65580 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____65580 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____65623 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____65660 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____65694 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____65705 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____65716 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___585_65734  ->
    match uu___585_65734 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____65746 = FStar_Syntax_Util.head_and_args t  in
    match uu____65746 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____65809 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____65811 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____65826 =
                     let uu____65828 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____65828  in
                   FStar_Util.format1 "@<%s>" uu____65826
                in
             let uu____65832 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____65809 uu____65811 uu____65832
         | uu____65835 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___586_65847  ->
      match uu___586_65847 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____65852 =
            let uu____65856 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____65858 =
              let uu____65862 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____65864 =
                let uu____65868 =
                  let uu____65872 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____65872]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____65868
                 in
              uu____65862 :: uu____65864  in
            uu____65856 :: uu____65858  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____65852
      | FStar_TypeChecker_Common.CProb p ->
          let uu____65883 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____65885 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____65887 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____65883
            uu____65885 (rel_to_string p.FStar_TypeChecker_Common.relation)
            uu____65887
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___587_65901  ->
      match uu___587_65901 with
      | UNIV (u,t) ->
          let x =
            let uu____65907 = FStar_Options.hide_uvar_nums ()  in
            if uu____65907
            then "?"
            else
              (let uu____65914 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____65914 FStar_Util.string_of_int)
             in
          let uu____65918 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____65918
      | TERM (u,t) ->
          let x =
            let uu____65925 = FStar_Options.hide_uvar_nums ()  in
            if uu____65925
            then "?"
            else
              (let uu____65932 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____65932 FStar_Util.string_of_int)
             in
          let uu____65936 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____65936
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____65955 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____65955 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____65976 =
      let uu____65980 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____65980
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____65976 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____65999 .
    (FStar_Syntax_Syntax.term * 'Auu____65999) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____66018 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____66039  ->
              match uu____66039 with
              | (x,uu____66046) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____66018 (FStar_String.concat " ")
  
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
        (let uu____66089 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____66089
         then
           let uu____66094 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____66094
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___588_66105  ->
    match uu___588_66105 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____66111 .
    'Auu____66111 FStar_TypeChecker_Common.problem ->
      'Auu____66111 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___722_66123 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___722_66123.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___722_66123.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___722_66123.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___722_66123.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___722_66123.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___722_66123.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___722_66123.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____66131 .
    'Auu____66131 FStar_TypeChecker_Common.problem ->
      'Auu____66131 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___589_66151  ->
    match uu___589_66151 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _66157  -> FStar_TypeChecker_Common.TProb _66157)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _66163  -> FStar_TypeChecker_Common.CProb _66163)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___590_66169  ->
    match uu___590_66169 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___734_66175 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___734_66175.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___734_66175.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___734_66175.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___734_66175.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___734_66175.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___734_66175.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___734_66175.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___734_66175.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___734_66175.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___738_66183 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___738_66183.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___738_66183.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___738_66183.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___738_66183.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___738_66183.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___738_66183.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___738_66183.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___738_66183.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___738_66183.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___591_66196  ->
      match uu___591_66196 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___592_66203  ->
    match uu___592_66203 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___593_66216  ->
    match uu___593_66216 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___594_66231  ->
    match uu___594_66231 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___595_66246  ->
    match uu___595_66246 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___596_66260  ->
    match uu___596_66260 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___597_66274  ->
    match uu___597_66274 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___598_66286  ->
    match uu___598_66286 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____66302 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____66302) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____66332 =
          let uu____66334 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66334  in
        if uu____66332
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____66371)::bs ->
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
          let uu____66418 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____66442 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____66442]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____66418
      | FStar_TypeChecker_Common.CProb p ->
          let uu____66470 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____66494 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____66494]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____66470
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____66541 =
          let uu____66543 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66543  in
        if uu____66541
        then ()
        else
          (let uu____66548 =
             let uu____66551 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____66551
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____66548 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____66600 =
          let uu____66602 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66602  in
        if uu____66600
        then ()
        else
          (let uu____66607 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____66607)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____66627 =
        let uu____66629 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____66629  in
      if uu____66627
      then ()
      else
        (let msgf m =
           let uu____66643 =
             let uu____66645 =
               let uu____66647 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____66647 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____66645  in
           Prims.op_Hat msg uu____66643  in
         (let uu____66652 = msgf "scope"  in
          let uu____66655 = p_scope prob  in
          def_scope_wf uu____66652 (p_loc prob) uu____66655);
         (let uu____66667 = msgf "guard"  in
          def_check_scoped uu____66667 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____66674 = msgf "lhs"  in
                def_check_scoped uu____66674 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____66677 = msgf "rhs"  in
                def_check_scoped uu____66677 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____66684 = msgf "lhs"  in
                def_check_scoped_comp uu____66684 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____66687 = msgf "rhs"  in
                def_check_scoped_comp uu____66687 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___831_66708 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___831_66708.wl_deferred);
          ctr = (uu___831_66708.ctr);
          defer_ok = (uu___831_66708.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___831_66708.umax_heuristic_ok);
          tcenv = (uu___831_66708.tcenv);
          wl_implicits = (uu___831_66708.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____66716 .
    FStar_TypeChecker_Env.env ->
      ('Auu____66716 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___835_66739 = empty_worklist env  in
      let uu____66740 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____66740;
        wl_deferred = (uu___835_66739.wl_deferred);
        ctr = (uu___835_66739.ctr);
        defer_ok = (uu___835_66739.defer_ok);
        smt_ok = (uu___835_66739.smt_ok);
        umax_heuristic_ok = (uu___835_66739.umax_heuristic_ok);
        tcenv = (uu___835_66739.tcenv);
        wl_implicits = (uu___835_66739.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___840_66763 = wl  in
        {
          attempting = (uu___840_66763.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___840_66763.ctr);
          defer_ok = (uu___840_66763.defer_ok);
          smt_ok = (uu___840_66763.smt_ok);
          umax_heuristic_ok = (uu___840_66763.umax_heuristic_ok);
          tcenv = (uu___840_66763.tcenv);
          wl_implicits = (uu___840_66763.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___845_66791 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___845_66791.wl_deferred);
         ctr = (uu___845_66791.ctr);
         defer_ok = (uu___845_66791.defer_ok);
         smt_ok = (uu___845_66791.smt_ok);
         umax_heuristic_ok = (uu___845_66791.umax_heuristic_ok);
         tcenv = (uu___845_66791.tcenv);
         wl_implicits = (uu___845_66791.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____66805 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____66805 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____66839 = FStar_Syntax_Util.type_u ()  in
            match uu____66839 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____66851 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____66851 with
                 | (uu____66869,tt,wl1) ->
                     let uu____66872 = FStar_Syntax_Util.mk_eq2 u tt t1 t2
                        in
                     (uu____66872, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___599_66878  ->
    match uu___599_66878 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _66884  -> FStar_TypeChecker_Common.TProb _66884) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _66890  -> FStar_TypeChecker_Common.CProb _66890) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____66898 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____66898 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____66918  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____67015 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____67015 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____67015 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____67015 FStar_TypeChecker_Common.problem *
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
                        let uu____67102 =
                          let uu____67111 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____67111]  in
                        FStar_List.append scope uu____67102
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____67154 =
                      let uu____67157 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____67157  in
                    FStar_List.append uu____67154
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____67176 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____67176 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____67202 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____67202;
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
                  (let uu____67276 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____67276 with
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
                  (let uu____67364 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____67364 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____67402 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____67402 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____67402 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____67402 FStar_TypeChecker_Common.problem *
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
                          let uu____67470 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____67470]  in
                        let uu____67489 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____67489
                     in
                  let uu____67492 =
                    let uu____67499 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___928_67510 = wl  in
                       {
                         attempting = (uu___928_67510.attempting);
                         wl_deferred = (uu___928_67510.wl_deferred);
                         ctr = (uu___928_67510.ctr);
                         defer_ok = (uu___928_67510.defer_ok);
                         smt_ok = (uu___928_67510.smt_ok);
                         umax_heuristic_ok =
                           (uu___928_67510.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___928_67510.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____67499
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____67492 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____67528 =
                              let uu____67533 =
                                let uu____67534 =
                                  let uu____67543 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____67543
                                   in
                                [uu____67534]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____67533
                               in
                            uu____67528 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____67573 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____67573;
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
                let uu____67621 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____67621;
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
  'Auu____67636 .
    worklist ->
      'Auu____67636 FStar_TypeChecker_Common.problem ->
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
              let uu____67669 =
                let uu____67672 =
                  let uu____67673 =
                    let uu____67680 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____67680)  in
                  FStar_Syntax_Syntax.NT uu____67673  in
                [uu____67672]  in
              FStar_Syntax_Subst.subst uu____67669 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____67704 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____67704
        then
          let uu____67712 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____67715 = prob_to_string env d  in
          let uu____67717 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____67712 uu____67715 uu____67717 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____67733 -> failwith "impossible"  in
           let uu____67736 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____67752 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____67754 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____67752, uu____67754)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____67761 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____67763 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____67761, uu____67763)
              in
           match uu____67736 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___600_67791  ->
            match uu___600_67791 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____67803 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____67807 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____67807 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___601_67838  ->
           match uu___601_67838 with
           | UNIV uu____67841 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____67848 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____67848
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
        (fun uu___602_67876  ->
           match uu___602_67876 with
           | UNIV (u',t) ->
               let uu____67881 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____67881
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____67888 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____67900 =
        let uu____67901 =
          let uu____67902 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____67902
           in
        FStar_Syntax_Subst.compress uu____67901  in
      FStar_All.pipe_right uu____67900 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____67914 =
        let uu____67915 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____67915  in
      FStar_All.pipe_right uu____67914 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____67923 = FStar_Syntax_Util.head_and_args t  in
    match uu____67923 with
    | (h,uu____67942) ->
        let uu____67967 =
          let uu____67968 = FStar_Syntax_Subst.compress h  in
          uu____67968.FStar_Syntax_Syntax.n  in
        (match uu____67967 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____67973 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____67986 = should_strongly_reduce t  in
      if uu____67986
      then
        let uu____67989 =
          let uu____67990 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____67990  in
        FStar_All.pipe_right uu____67989 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____68000 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____68000) ->
        (FStar_Syntax_Syntax.term * 'Auu____68000)
  =
  fun env  ->
    fun t  ->
      let uu____68023 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____68023, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____68075  ->
              match uu____68075 with
              | (x,imp) ->
                  let uu____68094 =
                    let uu___1025_68095 = x  in
                    let uu____68096 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1025_68095.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1025_68095.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____68096
                    }  in
                  (uu____68094, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____68120 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____68120
        | FStar_Syntax_Syntax.U_max us ->
            let uu____68124 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____68124
        | uu____68127 -> u2  in
      let uu____68128 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____68128
  
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
                (let uu____68249 = norm_refinement env t12  in
                 match uu____68249 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____68264;
                     FStar_Syntax_Syntax.vars = uu____68265;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____68289 =
                       let uu____68291 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____68293 = FStar_Syntax_Print.tag_of_term tt
                          in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____68291 uu____68293
                        in
                     failwith uu____68289)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____68309 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____68309
          | FStar_Syntax_Syntax.Tm_uinst uu____68310 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68347 =
                   let uu____68348 = FStar_Syntax_Subst.compress t1'  in
                   uu____68348.FStar_Syntax_Syntax.n  in
                 match uu____68347 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68363 -> aux true t1'
                 | uu____68371 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____68386 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68417 =
                   let uu____68418 = FStar_Syntax_Subst.compress t1'  in
                   uu____68418.FStar_Syntax_Syntax.n  in
                 match uu____68417 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68433 -> aux true t1'
                 | uu____68441 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____68456 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68503 =
                   let uu____68504 = FStar_Syntax_Subst.compress t1'  in
                   uu____68504.FStar_Syntax_Syntax.n  in
                 match uu____68503 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68519 -> aux true t1'
                 | uu____68527 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____68542 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____68557 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____68572 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____68587 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____68602 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____68631 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____68664 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____68685 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____68712 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____68740 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____68777 ->
              let uu____68784 =
                let uu____68786 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68788 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68786 uu____68788
                 in
              failwith uu____68784
          | FStar_Syntax_Syntax.Tm_ascribed uu____68803 ->
              let uu____68830 =
                let uu____68832 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68834 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68832 uu____68834
                 in
              failwith uu____68830
          | FStar_Syntax_Syntax.Tm_delayed uu____68849 ->
              let uu____68872 =
                let uu____68874 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68876 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68874 uu____68876
                 in
              failwith uu____68872
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____68891 =
                let uu____68893 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68895 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68893 uu____68895
                 in
              failwith uu____68891
           in
        let uu____68910 = whnf env t1  in aux false uu____68910
  
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
      let uu____68971 = base_and_refinement env t  in
      FStar_All.pipe_right uu____68971 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____69012 = FStar_Syntax_Syntax.null_bv t  in
    (uu____69012, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____69039 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____69039 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____69099  ->
    match uu____69099 with
    | (t_base,refopt) ->
        let uu____69130 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____69130 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____69172 =
      let uu____69176 =
        let uu____69179 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____69206  ->
                  match uu____69206 with | (uu____69215,uu____69216,x) -> x))
           in
        FStar_List.append wl.attempting uu____69179  in
      FStar_List.map (wl_prob_to_string wl) uu____69176  in
    FStar_All.pipe_right uu____69172 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____69239 .
    ('Auu____69239 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____69251  ->
    match uu____69251 with
    | (uu____69258,c,args) ->
        let uu____69261 = print_ctx_uvar c  in
        let uu____69263 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____69261 uu____69263
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____69273 = FStar_Syntax_Util.head_and_args t  in
    match uu____69273 with
    | (head1,_args) ->
        let uu____69317 =
          let uu____69318 = FStar_Syntax_Subst.compress head1  in
          uu____69318.FStar_Syntax_Syntax.n  in
        (match uu____69317 with
         | FStar_Syntax_Syntax.Tm_uvar uu____69322 -> true
         | uu____69336 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____69344 = FStar_Syntax_Util.head_and_args t  in
    match uu____69344 with
    | (head1,_args) ->
        let uu____69387 =
          let uu____69388 = FStar_Syntax_Subst.compress head1  in
          uu____69388.FStar_Syntax_Syntax.n  in
        (match uu____69387 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____69392) -> u
         | uu____69409 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____69434 = FStar_Syntax_Util.head_and_args t  in
      match uu____69434 with
      | (head1,args) ->
          let uu____69481 =
            let uu____69482 = FStar_Syntax_Subst.compress head1  in
            uu____69482.FStar_Syntax_Syntax.n  in
          (match uu____69481 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____69490)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____69523 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___603_69548  ->
                         match uu___603_69548 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____69553 =
                               let uu____69554 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____69554.FStar_Syntax_Syntax.n  in
                             (match uu____69553 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____69559 -> false)
                         | uu____69561 -> true))
                  in
               (match uu____69523 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____69586 =
                        FStar_List.collect
                          (fun uu___604_69598  ->
                             match uu___604_69598 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____69602 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____69602]
                             | uu____69603 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____69586 FStar_List.rev  in
                    let uu____69626 =
                      let uu____69633 =
                        let uu____69642 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___605_69664  ->
                                  match uu___605_69664 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____69668 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____69668]
                                  | uu____69669 -> []))
                           in
                        FStar_All.pipe_right uu____69642 FStar_List.rev  in
                      let uu____69692 =
                        let uu____69695 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____69695  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____69633 uu____69692
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____69626 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____69731  ->
                                match uu____69731 with
                                | (x,i) ->
                                    let uu____69750 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____69750, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____69781  ->
                                match uu____69781 with
                                | (a,i) ->
                                    let uu____69800 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____69800, i)) args_sol
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
           | uu____69822 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____69844 =
          let uu____69867 =
            let uu____69868 = FStar_Syntax_Subst.compress k  in
            uu____69868.FStar_Syntax_Syntax.n  in
          match uu____69867 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____69950 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____69950)
              else
                (let uu____69985 = FStar_Syntax_Util.abs_formals t  in
                 match uu____69985 with
                 | (ys',t1,uu____70018) ->
                     let uu____70023 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____70023))
          | uu____70062 ->
              let uu____70063 =
                let uu____70068 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____70068)  in
              ((ys, t), uu____70063)
           in
        match uu____69844 with
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
                 let uu____70163 = FStar_Syntax_Util.rename_binders xs ys1
                    in
                 FStar_Syntax_Subst.subst_comp uu____70163 c  in
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
               (let uu____70241 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____70241
                then
                  let uu____70246 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____70248 = print_ctx_uvar uv  in
                  let uu____70250 = FStar_Syntax_Print.term_to_string phi1
                     in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____70246 uu____70248 uu____70250
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____70259 =
                   let uu____70261 = FStar_Util.string_of_int (p_pid prob)
                      in
                   Prims.op_Hat "solve_prob'.sol." uu____70261  in
                 let uu____70264 =
                   let uu____70267 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____70267
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____70259 uu____70264 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____70300 =
               let uu____70301 =
                 let uu____70303 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____70305 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____70303 uu____70305
                  in
               failwith uu____70301  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____70371  ->
                       match uu____70371 with
                       | (a,i) ->
                           let uu____70392 =
                             let uu____70393 = FStar_Syntax_Subst.compress a
                                in
                             uu____70393.FStar_Syntax_Syntax.n  in
                           (match uu____70392 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____70419 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____70429 =
                 let uu____70431 = is_flex g  in
                 Prims.op_Negation uu____70431  in
               if uu____70429
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____70440 = destruct_flex_t g wl  in
                  match uu____70440 with
                  | ((uu____70445,uv1,args),wl1) ->
                      ((let uu____70450 = args_as_binders args  in
                        assign_solution uu____70450 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___1277_70452 = wl1  in
              {
                attempting = (uu___1277_70452.attempting);
                wl_deferred = (uu___1277_70452.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___1277_70452.defer_ok);
                smt_ok = (uu___1277_70452.smt_ok);
                umax_heuristic_ok = (uu___1277_70452.umax_heuristic_ok);
                tcenv = (uu___1277_70452.tcenv);
                wl_implicits = (uu___1277_70452.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____70477 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____70477
         then
           let uu____70482 = FStar_Util.string_of_int pid  in
           let uu____70484 =
             let uu____70486 = FStar_List.map (uvi_to_string wl.tcenv) sol
                in
             FStar_All.pipe_right uu____70486 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____70482
             uu____70484
         else ());
        commit sol;
        (let uu___1285_70500 = wl  in
         {
           attempting = (uu___1285_70500.attempting);
           wl_deferred = (uu___1285_70500.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___1285_70500.defer_ok);
           smt_ok = (uu___1285_70500.smt_ok);
           umax_heuristic_ok = (uu___1285_70500.umax_heuristic_ok);
           tcenv = (uu___1285_70500.tcenv);
           wl_implicits = (uu___1285_70500.wl_implicits)
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
             | (uu____70566,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____70594 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____70594
              in
           (let uu____70600 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____70600
            then
              let uu____70605 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____70609 =
                let uu____70611 =
                  FStar_List.map (uvi_to_string wl.tcenv) uvis  in
                FStar_All.pipe_right uu____70611 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____70605
                uu____70609
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
        let uu____70646 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____70646 FStar_Util.set_elements  in
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
      let uu____70686 = occurs uk t  in
      match uu____70686 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____70725 =
                 let uu____70727 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____70729 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____70727 uu____70729
                  in
               FStar_Pervasives_Native.Some uu____70725)
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
            let uu____70849 = maximal_prefix bs_tail bs'_tail  in
            (match uu____70849 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____70900 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____70957  ->
             match uu____70957 with
             | (x,uu____70969) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____70987 = FStar_List.last bs  in
      match uu____70987 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____71011) ->
          let uu____71022 =
            FStar_Util.prefix_until
              (fun uu___606_71037  ->
                 match uu___606_71037 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____71040 -> false) g
             in
          (match uu____71022 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____71054,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____71091 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____71091 with
        | (pfx,uu____71101) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____71113 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____71113 with
             | (uu____71121,src',wl1) ->
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
                 | uu____71235 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____71236 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____71300  ->
                  fun uu____71301  ->
                    match (uu____71300, uu____71301) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____71404 =
                          let uu____71406 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____71406
                           in
                        if uu____71404
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____71440 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____71440
                           then
                             let uu____71457 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____71457)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____71236 with | (isect,uu____71507) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____71543 'Auu____71544 .
    (FStar_Syntax_Syntax.bv * 'Auu____71543) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____71544) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____71602  ->
              fun uu____71603  ->
                match (uu____71602, uu____71603) with
                | ((a,uu____71622),(b,uu____71624)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____71640 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____71640) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____71671  ->
           match uu____71671 with
           | (y,uu____71678) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____71688 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____71688) Prims.list ->
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
                   let uu____71850 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____71850
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____71883 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____71935 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____71980 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____72002 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___607_72010  ->
    match uu___607_72010 with
    | MisMatch (d1,d2) ->
        let uu____72022 =
          let uu____72024 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____72026 =
            let uu____72028 =
              let uu____72030 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____72030 ")"  in
            Prims.op_Hat ") (" uu____72028  in
          Prims.op_Hat uu____72024 uu____72026  in
        Prims.op_Hat "MisMatch (" uu____72022
    | HeadMatch u ->
        let uu____72037 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____72037
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___608_72046  ->
    match uu___608_72046 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____72063 -> HeadMatch false
  
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
          let uu____72085 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____72085 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____72096 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____72120 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____72130 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____72157 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____72157
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____72158 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____72159 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____72160 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____72173 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____72187 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____72211) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____72217,uu____72218) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____72260) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____72285;
             FStar_Syntax_Syntax.index = uu____72286;
             FStar_Syntax_Syntax.sort = t2;_},uu____72288)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____72296 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____72297 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____72298 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____72313 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____72320 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____72340 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____72340
  
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
           { FStar_Syntax_Syntax.blob = uu____72359;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____72360;
             FStar_Syntax_Syntax.ltyp = uu____72361;
             FStar_Syntax_Syntax.rng = uu____72362;_},uu____72363)
            ->
            let uu____72374 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____72374 t21
        | (uu____72375,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____72376;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____72377;
             FStar_Syntax_Syntax.ltyp = uu____72378;
             FStar_Syntax_Syntax.rng = uu____72379;_})
            ->
            let uu____72390 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____72390
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____72402 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____72402
            then FullMatch
            else
              (let uu____72407 =
                 let uu____72416 =
                   let uu____72419 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____72419  in
                 let uu____72420 =
                   let uu____72423 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____72423  in
                 (uu____72416, uu____72420)  in
               MisMatch uu____72407)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____72429),FStar_Syntax_Syntax.Tm_uinst (g,uu____72431)) ->
            let uu____72440 = head_matches env f g  in
            FStar_All.pipe_right uu____72440 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____72441) -> HeadMatch true
        | (uu____72443,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____72447 = FStar_Const.eq_const c d  in
            if uu____72447
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____72457),FStar_Syntax_Syntax.Tm_uvar (uv',uu____72459)) ->
            let uu____72492 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____72492
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____72502),FStar_Syntax_Syntax.Tm_refine (y,uu____72504)) ->
            let uu____72513 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____72513 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____72515),uu____72516) ->
            let uu____72521 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____72521 head_match
        | (uu____72522,FStar_Syntax_Syntax.Tm_refine (x,uu____72524)) ->
            let uu____72529 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____72529 head_match
        | (FStar_Syntax_Syntax.Tm_type
           uu____72530,FStar_Syntax_Syntax.Tm_type uu____72531) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____72533,FStar_Syntax_Syntax.Tm_arrow uu____72534) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____72565),FStar_Syntax_Syntax.Tm_app
           (head',uu____72567)) ->
            let uu____72616 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____72616 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____72618),uu____72619) ->
            let uu____72644 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____72644 head_match
        | (uu____72645,FStar_Syntax_Syntax.Tm_app (head1,uu____72647)) ->
            let uu____72672 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____72672 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____72673,FStar_Syntax_Syntax.Tm_let
           uu____72674) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____72702,FStar_Syntax_Syntax.Tm_match uu____72703) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____72749,FStar_Syntax_Syntax.Tm_abs
           uu____72750) -> HeadMatch true
        | uu____72788 ->
            let uu____72793 =
              let uu____72802 = delta_depth_of_term env t11  in
              let uu____72805 = delta_depth_of_term env t21  in
              (uu____72802, uu____72805)  in
            MisMatch uu____72793
  
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
            (let uu____72871 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____72871
             then
               let uu____72876 = FStar_Syntax_Print.term_to_string t  in
               let uu____72878 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____72876 uu____72878
             else ());
            (let uu____72883 =
               let uu____72884 = FStar_Syntax_Util.un_uinst head1  in
               uu____72884.FStar_Syntax_Syntax.n  in
             match uu____72883 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____72890 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____72890 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____72904 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____72904
                        then
                          let uu____72909 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____72909
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____72914 ->
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
                      let uu____72931 =
                        let uu____72933 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____72933 = FStar_Syntax_Util.Equal  in
                      if uu____72931
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____72940 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____72940
                          then
                            let uu____72945 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____72947 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n"
                              uu____72945 uu____72947
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____72952 -> FStar_Pervasives_Native.None)
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
            (let uu____73104 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____73104
             then
               let uu____73109 = FStar_Syntax_Print.term_to_string t11  in
               let uu____73111 = FStar_Syntax_Print.term_to_string t21  in
               let uu____73113 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____73109
                 uu____73111 uu____73113
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____73141 =
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
               match uu____73141 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____73189 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____73189 with
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
                  uu____73227),uu____73228)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____73249 =
                      let uu____73258 = maybe_inline t11  in
                      let uu____73261 = maybe_inline t21  in
                      (uu____73258, uu____73261)  in
                    match uu____73249 with
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
                 (uu____73304,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____73305))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____73326 =
                      let uu____73335 = maybe_inline t11  in
                      let uu____73338 = maybe_inline t21  in
                      (uu____73335, uu____73338)  in
                    match uu____73326 with
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
             | MisMatch uu____73393 -> fail1 n_delta r t11 t21
             | uu____73402 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____73417 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____73417
           then
             let uu____73422 = FStar_Syntax_Print.term_to_string t1  in
             let uu____73424 = FStar_Syntax_Print.term_to_string t2  in
             let uu____73426 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____73434 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____73451 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____73451
                    (fun uu____73486  ->
                       match uu____73486 with
                       | (t11,t21) ->
                           let uu____73494 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____73496 =
                             let uu____73498 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____73498  in
                           Prims.op_Hat uu____73494 uu____73496))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____73422 uu____73424 uu____73426 uu____73434
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____73515 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____73515 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___609_73530  ->
    match uu___609_73530 with
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
      let uu___1789_73579 = p  in
      let uu____73582 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____73583 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1789_73579.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____73582;
        FStar_TypeChecker_Common.relation =
          (uu___1789_73579.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____73583;
        FStar_TypeChecker_Common.element =
          (uu___1789_73579.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1789_73579.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1789_73579.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1789_73579.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1789_73579.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1789_73579.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____73598 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____73598
            (fun _73603  -> FStar_TypeChecker_Common.TProb _73603)
      | FStar_TypeChecker_Common.CProb uu____73604 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____73627 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____73627 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____73635 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____73635 with
           | (lh,lhs_args) ->
               let uu____73682 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____73682 with
                | (rh,rhs_args) ->
                    let uu____73729 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73742,FStar_Syntax_Syntax.Tm_uvar uu____73743)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____73832 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____73859,uu____73860)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____73875,FStar_Syntax_Syntax.Tm_uvar uu____73876)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73891,FStar_Syntax_Syntax.Tm_arrow
                         uu____73892) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_73922 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_73922.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_73922.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_73922.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_73922.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_73922.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_73922.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_73922.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_73922.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_73922.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73925,FStar_Syntax_Syntax.Tm_type uu____73926)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_73942 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_73942.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_73942.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_73942.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_73942.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_73942.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_73942.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_73942.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_73942.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_73942.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____73945,FStar_Syntax_Syntax.Tm_uvar uu____73946)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_73962 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_73962.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_73962.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_73962.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_73962.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_73962.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_73962.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_73962.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_73962.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_73962.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____73965,FStar_Syntax_Syntax.Tm_uvar uu____73966)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____73981,uu____73982)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____73997,FStar_Syntax_Syntax.Tm_uvar uu____73998)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____74013,uu____74014) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____73729 with
                     | (rank,tp1) ->
                         let uu____74027 =
                           FStar_All.pipe_right
                             (let uu___1860_74031 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1860_74031.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1860_74031.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1860_74031.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1860_74031.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1860_74031.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1860_74031.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1860_74031.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1860_74031.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1860_74031.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _74034  ->
                                FStar_TypeChecker_Common.TProb _74034)
                            in
                         (rank, uu____74027))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____74038 =
            FStar_All.pipe_right
              (let uu___1864_74042 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1864_74042.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1864_74042.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1864_74042.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1864_74042.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1864_74042.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1864_74042.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1864_74042.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1864_74042.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1864_74042.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _74045  -> FStar_TypeChecker_Common.CProb _74045)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____74038)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____74105 probs =
      match uu____74105 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____74186 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____74207 = rank wl.tcenv hd1  in
               (match uu____74207 with
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
                      (let uu____74268 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____74273 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____74273)
                          in
                       if uu____74268
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
          let uu____74346 = FStar_Syntax_Util.head_and_args t  in
          match uu____74346 with
          | (hd1,uu____74365) ->
              let uu____74390 =
                let uu____74391 = FStar_Syntax_Subst.compress hd1  in
                uu____74391.FStar_Syntax_Syntax.n  in
              (match uu____74390 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____74396) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____74431  ->
                           match uu____74431 with
                           | (y,uu____74440) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____74463  ->
                                       match uu____74463 with
                                       | (x,uu____74472) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____74477 -> false)
           in
        let uu____74479 = rank tcenv p  in
        match uu____74479 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____74488 -> true
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
    match projectee with | UDeferred _0 -> true | uu____74525 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____74545 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____74566 -> false
  
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
                        let uu____74629 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____74629 with
                        | (k,uu____74637) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____74650 -> false)))
            | uu____74652 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____74704 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____74712 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____74712 = (Prims.parse_int "0")))
                           in
                        if uu____74704 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____74733 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____74741 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____74741 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____74733)
               in
            let uu____74745 = filter1 u12  in
            let uu____74748 = filter1 u22  in (uu____74745, uu____74748)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____74783 = filter_out_common_univs us1 us2  in
                   (match uu____74783 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____74843 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____74843 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____74846 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____74857 =
                             let uu____74859 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____74861 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____74859 uu____74861
                              in
                           UFailed uu____74857))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____74887 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____74887 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____74913 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____74913 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____74916 ->
                   let uu____74921 =
                     let uu____74923 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____74925 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)"
                       uu____74923 uu____74925 msg
                      in
                   UFailed uu____74921)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____74928,uu____74929) ->
              let uu____74931 =
                let uu____74933 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____74935 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____74933 uu____74935
                 in
              failwith uu____74931
          | (FStar_Syntax_Syntax.U_unknown ,uu____74938) ->
              let uu____74939 =
                let uu____74941 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____74943 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____74941 uu____74943
                 in
              failwith uu____74939
          | (uu____74946,FStar_Syntax_Syntax.U_bvar uu____74947) ->
              let uu____74949 =
                let uu____74951 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____74953 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____74951 uu____74953
                 in
              failwith uu____74949
          | (uu____74956,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____74957 =
                let uu____74959 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____74961 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____74959 uu____74961
                 in
              failwith uu____74957
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____74991 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____74991
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____75008 = occurs_univ v1 u3  in
              if uu____75008
              then
                let uu____75011 =
                  let uu____75013 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____75015 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____75013 uu____75015
                   in
                try_umax_components u11 u21 uu____75011
              else
                (let uu____75020 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____75020)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____75032 = occurs_univ v1 u3  in
              if uu____75032
              then
                let uu____75035 =
                  let uu____75037 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____75039 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____75037 uu____75039
                   in
                try_umax_components u11 u21 uu____75035
              else
                (let uu____75044 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____75044)
          | (FStar_Syntax_Syntax.U_max uu____75045,uu____75046) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____75054 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____75054
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____75060,FStar_Syntax_Syntax.U_max uu____75061) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____75069 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____75069
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____75075,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____75077,FStar_Syntax_Syntax.U_name uu____75078) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____75080) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____75082) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____75084,FStar_Syntax_Syntax.U_succ uu____75085) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____75087,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____75194 = bc1  in
      match uu____75194 with
      | (bs1,mk_cod1) ->
          let uu____75238 = bc2  in
          (match uu____75238 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____75349 = aux xs ys  in
                     (match uu____75349 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____75432 =
                       let uu____75439 = mk_cod1 xs  in ([], uu____75439)  in
                     let uu____75442 =
                       let uu____75449 = mk_cod2 ys  in ([], uu____75449)  in
                     (uu____75432, uu____75442)
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
                  let uu____75518 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____75518 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____75521 =
                    let uu____75522 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____75522 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____75521
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____75527 = has_type_guard t1 t2  in (uu____75527, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____75528 = has_type_guard t2 t1  in (uu____75528, wl)
  
let is_flex_pat :
  'Auu____75538 'Auu____75539 'Auu____75540 .
    ('Auu____75538 * 'Auu____75539 * 'Auu____75540 Prims.list) -> Prims.bool
  =
  fun uu___610_75554  ->
    match uu___610_75554 with
    | (uu____75563,uu____75564,[]) -> true
    | uu____75568 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____75601 = f  in
      match uu____75601 with
      | (uu____75608,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____75609;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____75610;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____75613;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____75614;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____75615;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____75616;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____75686  ->
                 match uu____75686 with
                 | (y,uu____75695) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____75849 =
                  let uu____75864 =
                    let uu____75867 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____75867  in
                  ((FStar_List.rev pat_binders), uu____75864)  in
                FStar_Pervasives_Native.Some uu____75849
            | (uu____75900,[]) ->
                let uu____75931 =
                  let uu____75946 =
                    let uu____75949 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____75949  in
                  ((FStar_List.rev pat_binders), uu____75946)  in
                FStar_Pervasives_Native.Some uu____75931
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____76040 =
                  let uu____76041 = FStar_Syntax_Subst.compress a  in
                  uu____76041.FStar_Syntax_Syntax.n  in
                (match uu____76040 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____76061 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____76061
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___2188_76091 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___2188_76091.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___2188_76091.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____76095 =
                            let uu____76096 =
                              let uu____76103 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____76103)  in
                            FStar_Syntax_Syntax.NT uu____76096  in
                          [uu____76095]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___2194_76119 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2194_76119.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2194_76119.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____76120 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____76160 =
                  let uu____76175 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____76175  in
                (match uu____76160 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____76250 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____76283 ->
               let uu____76284 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____76284 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____76606 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____76606
       then
         let uu____76611 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____76611
       else ());
      (let uu____76616 = next_prob probs  in
       match uu____76616 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___2219_76643 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___2219_76643.wl_deferred);
               ctr = (uu___2219_76643.ctr);
               defer_ok = (uu___2219_76643.defer_ok);
               smt_ok = (uu___2219_76643.smt_ok);
               umax_heuristic_ok = (uu___2219_76643.umax_heuristic_ok);
               tcenv = (uu___2219_76643.tcenv);
               wl_implicits = (uu___2219_76643.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____76652 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____76652
                 then
                   let uu____76655 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____76655
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
                           (let uu___2231_76667 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___2231_76667.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___2231_76667.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___2231_76667.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___2231_76667.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___2231_76667.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___2231_76667.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___2231_76667.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___2231_76667.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___2231_76667.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____76693 ->
                let uu____76704 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____76775  ->
                          match uu____76775 with
                          | (c,uu____76786,uu____76787) -> c < probs.ctr))
                   in
                (match uu____76704 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____76842 =
                            let uu____76847 =
                              FStar_List.map
                                (fun uu____76865  ->
                                   match uu____76865 with
                                   | (uu____76879,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____76847, (probs.wl_implicits))  in
                          Success uu____76842
                      | uu____76887 ->
                          let uu____76898 =
                            let uu___2249_76899 = probs  in
                            let uu____76900 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____76923  ->
                                      match uu____76923 with
                                      | (uu____76932,uu____76933,y) -> y))
                               in
                            {
                              attempting = uu____76900;
                              wl_deferred = rest;
                              ctr = (uu___2249_76899.ctr);
                              defer_ok = (uu___2249_76899.defer_ok);
                              smt_ok = (uu___2249_76899.smt_ok);
                              umax_heuristic_ok =
                                (uu___2249_76899.umax_heuristic_ok);
                              tcenv = (uu___2249_76899.tcenv);
                              wl_implicits = (uu___2249_76899.wl_implicits)
                            }  in
                          solve env uu____76898))))

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
            let uu____76944 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____76944 with
            | USolved wl1 ->
                let uu____76946 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____76946
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
                  let uu____77000 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____77000 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____77003 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____77016;
                  FStar_Syntax_Syntax.vars = uu____77017;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____77020;
                  FStar_Syntax_Syntax.vars = uu____77021;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____77034,uu____77035) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____77043,FStar_Syntax_Syntax.Tm_uinst uu____77044) ->
                failwith "Impossible: expect head symbols to match"
            | uu____77052 -> USolved wl

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
            ((let uu____77064 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____77064
              then
                let uu____77069 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____77069 msg
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
               let uu____77161 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____77161 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____77216 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____77216
                then
                  let uu____77221 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____77223 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____77221 uu____77223
                else ());
               (let uu____77228 = head_matches_delta env1 wl2 t1 t2  in
                match uu____77228 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____77274 = eq_prob t1 t2 wl2  in
                         (match uu____77274 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____77295 ->
                         let uu____77304 = eq_prob t1 t2 wl2  in
                         (match uu____77304 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____77354 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____77369 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____77370 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____77369, uu____77370)
                           | FStar_Pervasives_Native.None  ->
                               let uu____77375 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____77376 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____77375, uu____77376)
                            in
                         (match uu____77354 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____77407 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____77407 with
                                | (t1_hd,t1_args) ->
                                    let uu____77452 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____77452 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____77518 =
                                              let uu____77525 =
                                                let uu____77536 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____77536 :: t1_args  in
                                              let uu____77553 =
                                                let uu____77562 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____77562 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____77611  ->
                                                   fun uu____77612  ->
                                                     fun uu____77613  ->
                                                       match (uu____77611,
                                                               uu____77612,
                                                               uu____77613)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____77663),
                                                          (a2,uu____77665))
                                                           ->
                                                           let uu____77702 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____77702
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____77525
                                                uu____77553
                                               in
                                            match uu____77518 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___2403_77728 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___2403_77728.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___2403_77728.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___2403_77728.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____77740 =
                                                  solve env1 wl'  in
                                                (match uu____77740 with
                                                 | Success (uu____77743,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___2412_77747
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___2412_77747.attempting);
                                                            wl_deferred =
                                                              (uu___2412_77747.wl_deferred);
                                                            ctr =
                                                              (uu___2412_77747.ctr);
                                                            defer_ok =
                                                              (uu___2412_77747.defer_ok);
                                                            smt_ok =
                                                              (uu___2412_77747.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___2412_77747.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___2412_77747.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____77748 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____77781 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____77781 with
                                | (t1_base,p1_opt) ->
                                    let uu____77817 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____77817 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____77916 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____77916
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
                                               let uu____77969 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____77969
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
                                               let uu____78001 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____78001
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
                                               let uu____78033 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____78033
                                           | uu____78036 -> t_base  in
                                         let uu____78053 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____78053 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____78067 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____78067, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____78074 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____78074 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____78110 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____78110 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____78146 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____78146
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
                              let uu____78170 = combine t11 t21 wl2  in
                              (match uu____78170 with
                               | (t12,ps,wl3) ->
                                   ((let uu____78203 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____78203
                                     then
                                       let uu____78208 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____78208
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____78250 ts1 =
               match uu____78250 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____78313 = pairwise out t wl2  in
                        (match uu____78313 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____78349 =
               let uu____78360 = FStar_List.hd ts  in (uu____78360, [], wl1)
                in
             let uu____78369 = FStar_List.tl ts  in
             aux uu____78349 uu____78369  in
           let uu____78376 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____78376 with
           | (this_flex,this_rigid) ->
               let uu____78402 =
                 let uu____78403 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____78403.FStar_Syntax_Syntax.n  in
               (match uu____78402 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____78428 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____78428
                    then
                      let uu____78431 = destruct_flex_t this_flex wl  in
                      (match uu____78431 with
                       | (flex,wl1) ->
                           let uu____78438 = quasi_pattern env flex  in
                           (match uu____78438 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____78457 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____78457
                                  then
                                    let uu____78462 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____78462
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____78469 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2514_78472 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2514_78472.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2514_78472.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2514_78472.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2514_78472.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2514_78472.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2514_78472.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2514_78472.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2514_78472.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2514_78472.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____78469)
                | uu____78473 ->
                    ((let uu____78475 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____78475
                      then
                        let uu____78480 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____78480
                      else ());
                     (let uu____78485 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____78485 with
                      | (u,_args) ->
                          let uu____78528 =
                            let uu____78529 = FStar_Syntax_Subst.compress u
                               in
                            uu____78529.FStar_Syntax_Syntax.n  in
                          (match uu____78528 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____78557 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____78557 with
                                 | (u',uu____78576) ->
                                     let uu____78601 =
                                       let uu____78602 = whnf env u'  in
                                       uu____78602.FStar_Syntax_Syntax.n  in
                                     (match uu____78601 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____78624 -> false)
                                  in
                               let uu____78626 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___611_78649  ->
                                         match uu___611_78649 with
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
                                              | uu____78663 -> false)
                                         | uu____78667 -> false))
                                  in
                               (match uu____78626 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____78682 = whnf env this_rigid
                                         in
                                      let uu____78683 =
                                        FStar_List.collect
                                          (fun uu___612_78689  ->
                                             match uu___612_78689 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____78695 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____78695]
                                             | uu____78699 -> [])
                                          bounds_probs
                                         in
                                      uu____78682 :: uu____78683  in
                                    let uu____78700 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____78700 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____78733 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____78748 =
                                               let uu____78749 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____78749.FStar_Syntax_Syntax.n
                                                in
                                             match uu____78748 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____78761 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____78761)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____78772 -> bound  in
                                           let uu____78773 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____78773)  in
                                         (match uu____78733 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____78808 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____78808
                                                then
                                                  let wl'1 =
                                                    let uu___2574_78814 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2574_78814.wl_deferred);
                                                      ctr =
                                                        (uu___2574_78814.ctr);
                                                      defer_ok =
                                                        (uu___2574_78814.defer_ok);
                                                      smt_ok =
                                                        (uu___2574_78814.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2574_78814.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2574_78814.tcenv);
                                                      wl_implicits =
                                                        (uu___2574_78814.wl_implicits)
                                                    }  in
                                                  let uu____78815 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____78815
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____78821 =
                                                  solve_t env eq_prob
                                                    (let uu___2579_78823 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2579_78823.wl_deferred);
                                                       ctr =
                                                         (uu___2579_78823.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2579_78823.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2579_78823.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2579_78823.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____78821 with
                                                | Success (uu____78825,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2585_78828 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2585_78828.wl_deferred);
                                                        ctr =
                                                          (uu___2585_78828.ctr);
                                                        defer_ok =
                                                          (uu___2585_78828.defer_ok);
                                                        smt_ok =
                                                          (uu___2585_78828.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2585_78828.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2585_78828.tcenv);
                                                        wl_implicits =
                                                          (uu___2585_78828.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2588_78830 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2588_78830.attempting);
                                                        wl_deferred =
                                                          (uu___2588_78830.wl_deferred);
                                                        ctr =
                                                          (uu___2588_78830.ctr);
                                                        defer_ok =
                                                          (uu___2588_78830.defer_ok);
                                                        smt_ok =
                                                          (uu___2588_78830.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2588_78830.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2588_78830.tcenv);
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
                                                    let uu____78846 =
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
                                                    ((let uu____78860 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____78860
                                                      then
                                                        let uu____78865 =
                                                          let uu____78867 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____78867
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____78865
                                                      else ());
                                                     (let uu____78880 =
                                                        let uu____78895 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____78895)
                                                         in
                                                      match uu____78880 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____78917))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____78943 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____78943
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
                                                                  let uu____78963
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____78963))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____78988 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____78988
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
                                                                    let uu____79008
                                                                    =
                                                                    let uu____79013
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____79013
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____79008
                                                                    [] wl2
                                                                     in
                                                                  let uu____79019
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____79019))))
                                                      | uu____79020 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____79036 when flip ->
                               let uu____79037 =
                                 let uu____79039 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____79041 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____79039 uu____79041
                                  in
                               failwith uu____79037
                           | uu____79044 ->
                               let uu____79045 =
                                 let uu____79047 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____79049 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____79047 uu____79049
                                  in
                               failwith uu____79045)))))

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
                      (fun uu____79085  ->
                         match uu____79085 with
                         | (x,i) ->
                             let uu____79104 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____79104, i)) bs_lhs
                     in
                  let uu____79107 = lhs  in
                  match uu____79107 with
                  | (uu____79108,u_lhs,uu____79110) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____79207 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____79217 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____79217, univ)
                             in
                          match uu____79207 with
                          | (k,univ) ->
                              let uu____79224 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____79224 with
                               | (uu____79241,u,wl3) ->
                                   let uu____79244 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____79244, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____79270 =
                              let uu____79283 =
                                let uu____79294 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____79294 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____79345  ->
                                   fun uu____79346  ->
                                     match (uu____79345, uu____79346) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____79447 =
                                           let uu____79454 =
                                             let uu____79457 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____79457
                                              in
                                           copy_uvar u_lhs [] uu____79454 wl2
                                            in
                                         (match uu____79447 with
                                          | (uu____79486,t_a,wl3) ->
                                              let uu____79489 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____79489 with
                                               | (uu____79508,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____79283
                                ([], wl1)
                               in
                            (match uu____79270 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2698_79564 = ct  in
                                   let uu____79565 =
                                     let uu____79568 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____79568
                                      in
                                   let uu____79583 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2698_79564.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2698_79564.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____79565;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____79583;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2698_79564.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2701_79601 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2701_79601.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2701_79601.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____79604 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____79604 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____79666 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____79666 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____79677 =
                                          let uu____79682 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____79682)  in
                                        TERM uu____79677  in
                                      let uu____79683 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____79683 with
                                       | (sub_prob,wl3) ->
                                           let uu____79697 =
                                             let uu____79698 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____79698
                                              in
                                           solve env uu____79697))
                             | (x,imp)::formals2 ->
                                 let uu____79720 =
                                   let uu____79727 =
                                     let uu____79730 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____79730
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____79727 wl1
                                    in
                                 (match uu____79720 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____79751 =
                                          let uu____79754 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____79754
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____79751 u_x
                                         in
                                      let uu____79755 =
                                        let uu____79758 =
                                          let uu____79761 =
                                            let uu____79762 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____79762, imp)  in
                                          [uu____79761]  in
                                        FStar_List.append bs_terms
                                          uu____79758
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____79755 formals2 wl2)
                              in
                           let uu____79789 = occurs_check u_lhs arrow1  in
                           (match uu____79789 with
                            | (uu____79802,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____79818 =
                                    let uu____79820 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____79820
                                     in
                                  giveup_or_defer env orig wl uu____79818
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
              (let uu____79853 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____79853
               then
                 let uu____79858 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____79861 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____79858 (rel_to_string (p_rel orig)) uu____79861
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____79988 = rhs wl1 scope env1 subst1  in
                     (match uu____79988 with
                      | (rhs_prob,wl2) ->
                          ((let uu____80009 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____80009
                            then
                              let uu____80014 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____80014
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____80092 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____80092 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2770_80094 = hd1  in
                       let uu____80095 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2770_80094.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2770_80094.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____80095
                       }  in
                     let hd21 =
                       let uu___2773_80099 = hd2  in
                       let uu____80100 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2773_80099.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2773_80099.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____80100
                       }  in
                     let uu____80103 =
                       let uu____80108 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____80108
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____80103 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____80129 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____80129
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____80136 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____80136 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____80203 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____80203
                                  in
                               ((let uu____80221 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____80221
                                 then
                                   let uu____80226 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____80228 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____80226
                                     uu____80228
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____80261 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____80297 = aux wl [] env [] bs1 bs2  in
               match uu____80297 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____80352 = attempt sub_probs wl2  in
                   solve env uu____80352)

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
            let uu___2808_80373 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2808_80373.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2808_80373.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____80386 = try_solve env wl'  in
          match uu____80386 with
          | Success (uu____80387,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2817_80391 = wl  in
                  {
                    attempting = (uu___2817_80391.attempting);
                    wl_deferred = (uu___2817_80391.wl_deferred);
                    ctr = (uu___2817_80391.ctr);
                    defer_ok = (uu___2817_80391.defer_ok);
                    smt_ok = (uu___2817_80391.smt_ok);
                    umax_heuristic_ok = (uu___2817_80391.umax_heuristic_ok);
                    tcenv = (uu___2817_80391.tcenv);
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
        (let uu____80403 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____80403 wl)

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
              let uu____80417 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____80417 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____80451 = lhs1  in
              match uu____80451 with
              | (uu____80454,ctx_u,uu____80456) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____80464 ->
                        let uu____80465 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____80465 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____80514 = quasi_pattern env1 lhs1  in
              match uu____80514 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____80548) ->
                  let uu____80553 = lhs1  in
                  (match uu____80553 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____80568 = occurs_check ctx_u rhs1  in
                       (match uu____80568 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____80619 =
                                let uu____80627 =
                                  let uu____80629 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____80629
                                   in
                                FStar_Util.Inl uu____80627  in
                              (uu____80619, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____80657 =
                                 let uu____80659 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____80659  in
                               if uu____80657
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____80686 =
                                    let uu____80694 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____80694  in
                                  let uu____80700 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____80686, uu____80700)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____80744 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____80744 with
              | (rhs_hd,args) ->
                  let uu____80787 = FStar_Util.prefix args  in
                  (match uu____80787 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____80859 = lhs1  in
                       (match uu____80859 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____80863 =
                              let uu____80874 =
                                let uu____80881 =
                                  let uu____80884 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____80884
                                   in
                                copy_uvar u_lhs [] uu____80881 wl1  in
                              match uu____80874 with
                              | (uu____80911,t_last_arg,wl2) ->
                                  let uu____80914 =
                                    let uu____80921 =
                                      let uu____80922 =
                                        let uu____80931 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____80931]  in
                                      FStar_List.append bs_lhs uu____80922
                                       in
                                    copy_uvar u_lhs uu____80921 t_res_lhs wl2
                                     in
                                  (match uu____80914 with
                                   | (uu____80966,lhs',wl3) ->
                                       let uu____80969 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____80969 with
                                        | (uu____80986,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____80863 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____81007 =
                                     let uu____81008 =
                                       let uu____81013 =
                                         let uu____81014 =
                                           let uu____81017 =
                                             let uu____81022 =
                                               let uu____81023 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____81023]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____81022
                                              in
                                           uu____81017
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____81014
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____81013)  in
                                     TERM uu____81008  in
                                   [uu____81007]  in
                                 let uu____81050 =
                                   let uu____81057 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____81057 with
                                   | (p1,wl3) ->
                                       let uu____81077 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____81077 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____81050 with
                                  | (sub_probs,wl3) ->
                                      let uu____81109 =
                                        let uu____81110 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____81110  in
                                      solve env1 uu____81109))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____81144 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____81144 with
                | (uu____81162,args) ->
                    (match args with | [] -> false | uu____81198 -> true)
                 in
              let is_arrow rhs2 =
                let uu____81217 =
                  let uu____81218 = FStar_Syntax_Subst.compress rhs2  in
                  uu____81218.FStar_Syntax_Syntax.n  in
                match uu____81217 with
                | FStar_Syntax_Syntax.Tm_arrow uu____81222 -> true
                | uu____81238 -> false  in
              let uu____81240 = quasi_pattern env1 lhs1  in
              match uu____81240 with
              | FStar_Pervasives_Native.None  ->
                  let uu____81251 =
                    let uu____81253 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____81253
                     in
                  giveup_or_defer env1 orig1 wl1 uu____81251
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____81262 = is_app rhs1  in
                  if uu____81262
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____81267 = is_arrow rhs1  in
                     if uu____81267
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____81272 =
                          let uu____81274 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____81274
                           in
                        giveup_or_defer env1 orig1 wl1 uu____81272))
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
                let uu____81285 = lhs  in
                (match uu____81285 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____81289 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____81289 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____81307 =
                              let uu____81311 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____81311
                               in
                            FStar_All.pipe_right uu____81307
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____81332 = occurs_check ctx_uv rhs1  in
                          (match uu____81332 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____81361 =
                                   let uu____81363 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____81363
                                    in
                                 giveup_or_defer env orig wl uu____81361
                               else
                                 (let uu____81369 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____81369
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____81376 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____81376
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____81380 =
                                         let uu____81382 =
                                           names_to_string1 fvs2  in
                                         let uu____81384 =
                                           names_to_string1 fvs1  in
                                         let uu____81386 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____81382 uu____81384
                                           uu____81386
                                          in
                                       giveup_or_defer env orig wl
                                         uu____81380)
                                    else first_order orig env wl lhs rhs1))
                      | uu____81398 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____81405 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____81405 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____81431 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____81431
                             | (FStar_Util.Inl msg,uu____81433) ->
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
                  (let uu____81478 =
                     let uu____81495 = quasi_pattern env lhs  in
                     let uu____81502 = quasi_pattern env rhs  in
                     (uu____81495, uu____81502)  in
                   match uu____81478 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____81545 = lhs  in
                       (match uu____81545 with
                        | ({ FStar_Syntax_Syntax.n = uu____81546;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____81548;_},u_lhs,uu____81550)
                            ->
                            let uu____81553 = rhs  in
                            (match uu____81553 with
                             | (uu____81554,u_rhs,uu____81556) ->
                                 let uu____81557 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____81557
                                 then
                                   let uu____81564 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____81564
                                 else
                                   (let uu____81567 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____81567 with
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
                                        let uu____81599 =
                                          let uu____81606 =
                                            let uu____81609 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____81609
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____81606
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____81599 with
                                         | (uu____81621,w,wl1) ->
                                             let w_app =
                                               let uu____81627 =
                                                 let uu____81632 =
                                                   FStar_List.map
                                                     (fun uu____81643  ->
                                                        match uu____81643
                                                        with
                                                        | (z,uu____81651) ->
                                                            let uu____81656 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____81656) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____81632
                                                  in
                                               uu____81627
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____81660 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____81660
                                               then
                                                 let uu____81665 =
                                                   let uu____81669 =
                                                     flex_t_to_string lhs  in
                                                   let uu____81671 =
                                                     let uu____81675 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____81677 =
                                                       let uu____81681 =
                                                         term_to_string w  in
                                                       let uu____81683 =
                                                         let uu____81687 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____81696 =
                                                           let uu____81700 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____81709 =
                                                             let uu____81713
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____81713]
                                                              in
                                                           uu____81700 ::
                                                             uu____81709
                                                            in
                                                         uu____81687 ::
                                                           uu____81696
                                                          in
                                                       uu____81681 ::
                                                         uu____81683
                                                        in
                                                     uu____81675 ::
                                                       uu____81677
                                                      in
                                                   uu____81669 :: uu____81671
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____81665
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____81730 =
                                                     let uu____81735 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____81735)  in
                                                   TERM uu____81730  in
                                                 let uu____81736 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____81736
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____81744 =
                                                        let uu____81749 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____81749)
                                                         in
                                                      TERM uu____81744  in
                                                    [s1; s2])
                                                  in
                                               let uu____81750 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____81750))))))
                   | uu____81751 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____81822 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____81822
            then
              let uu____81827 = FStar_Syntax_Print.term_to_string t1  in
              let uu____81829 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____81831 = FStar_Syntax_Print.term_to_string t2  in
              let uu____81833 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____81827 uu____81829 uu____81831 uu____81833
            else ());
           (let uu____81844 = FStar_Syntax_Util.head_and_args t1  in
            match uu____81844 with
            | (head1,args1) ->
                let uu____81887 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____81887 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____81957 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____81957 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____81987 =
                         let uu____81989 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____81991 = args_to_string args1  in
                         let uu____81995 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____81997 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____81989 uu____81991 uu____81995 uu____81997
                          in
                       giveup env1 uu____81987 orig
                     else
                       (let uu____82004 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____82013 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____82013 = FStar_Syntax_Util.Equal)
                           in
                        if uu____82004
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___3066_82017 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___3066_82017.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___3066_82017.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___3066_82017.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___3066_82017.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___3066_82017.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___3066_82017.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___3066_82017.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___3066_82017.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____82027 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____82027
                                    else solve env1 wl2))
                        else
                          (let uu____82032 = base_and_refinement env1 t1  in
                           match uu____82032 with
                           | (base1,refinement1) ->
                               let uu____82057 = base_and_refinement env1 t2
                                  in
                               (match uu____82057 with
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
                                           let uu____82222 =
                                             FStar_List.fold_right
                                               (fun uu____82262  ->
                                                  fun uu____82263  ->
                                                    match (uu____82262,
                                                            uu____82263)
                                                    with
                                                    | (((a1,uu____82315),
                                                        (a2,uu____82317)),
                                                       (probs,wl3)) ->
                                                        let uu____82366 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____82366
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____82222 with
                                           | (subprobs,wl3) ->
                                               ((let uu____82409 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____82409
                                                 then
                                                   let uu____82414 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____82414
                                                 else ());
                                                (let uu____82420 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____82420
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
                                                    (let uu____82447 =
                                                       mk_sub_probs wl3  in
                                                     match uu____82447 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____82463 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____82463
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____82471 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____82471))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____82495 =
                                                    mk_sub_probs wl3  in
                                                  match uu____82495 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____82509 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____82509)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____82535 =
                                           match uu____82535 with
                                           | (prob,reason) ->
                                               ((let uu____82546 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____82546
                                                 then
                                                   let uu____82551 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____82553 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____82551 uu____82553
                                                     reason
                                                 else ());
                                                (let uu____82558 =
                                                   let uu____82567 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____82570 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____82567, uu____82570)
                                                    in
                                                 match uu____82558 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____82583 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____82583 with
                                                      | (head1',uu____82601)
                                                          ->
                                                          let uu____82626 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____82626
                                                           with
                                                           | (head2',uu____82644)
                                                               ->
                                                               let uu____82669
                                                                 =
                                                                 let uu____82674
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____82675
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____82674,
                                                                   uu____82675)
                                                                  in
                                                               (match uu____82669
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____82677
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____82677
                                                                    then
                                                                    let uu____82682
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____82684
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____82686
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____82688
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____82682
                                                                    uu____82684
                                                                    uu____82686
                                                                    uu____82688
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____82693
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___3152_82701
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___3152_82701.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___3152_82701.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___3152_82701.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___3152_82701.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___3152_82701.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___3152_82701.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___3152_82701.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___3152_82701.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____82703
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____82703
                                                                    then
                                                                    let uu____82708
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____82708
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____82713 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____82725 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____82725 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____82733 =
                                             let uu____82734 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____82734.FStar_Syntax_Syntax.n
                                              in
                                           match uu____82733 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____82739 -> false  in
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
                                          | uu____82742 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____82745 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___3172_82781 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___3172_82781.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___3172_82781.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___3172_82781.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___3172_82781.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___3172_82781.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___3172_82781.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___3172_82781.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___3172_82781.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____82857 = destruct_flex_t scrutinee wl1  in
             match uu____82857 with
             | ((_t,uv,_args),wl2) ->
                 let uu____82868 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____82868 with
                  | (xs,pat_term,uu____82884,uu____82885) ->
                      let uu____82890 =
                        FStar_List.fold_left
                          (fun uu____82913  ->
                             fun x  ->
                               match uu____82913 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____82934 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____82934 with
                                    | (uu____82953,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____82890 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____82974 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____82974 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___3212_82991 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___3212_82991.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___3212_82991.umax_heuristic_ok);
                                    tcenv = (uu___3212_82991.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____83003 = solve env1 wl'  in
                                (match uu____83003 with
                                 | Success (uu____83006,imps) ->
                                     let wl'1 =
                                       let uu___3220_83009 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___3220_83009.wl_deferred);
                                         ctr = (uu___3220_83009.ctr);
                                         defer_ok =
                                           (uu___3220_83009.defer_ok);
                                         smt_ok = (uu___3220_83009.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___3220_83009.umax_heuristic_ok);
                                         tcenv = (uu___3220_83009.tcenv);
                                         wl_implicits =
                                           (uu___3220_83009.wl_implicits)
                                       }  in
                                     let uu____83010 = solve env1 wl'1  in
                                     (match uu____83010 with
                                      | Success (uu____83013,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___3228_83017 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___3228_83017.attempting);
                                                 wl_deferred =
                                                   (uu___3228_83017.wl_deferred);
                                                 ctr = (uu___3228_83017.ctr);
                                                 defer_ok =
                                                   (uu___3228_83017.defer_ok);
                                                 smt_ok =
                                                   (uu___3228_83017.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3228_83017.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3228_83017.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____83018 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____83025 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____83048 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____83048
                 then
                   let uu____83053 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____83055 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____83053 uu____83055
                 else ());
                (let uu____83060 =
                   let uu____83081 =
                     let uu____83090 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____83090)  in
                   let uu____83097 =
                     let uu____83106 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____83106)  in
                   (uu____83081, uu____83097)  in
                 match uu____83060 with
                 | ((uu____83136,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____83139;
                                   FStar_Syntax_Syntax.vars = uu____83140;_}),
                    (s,t)) ->
                     let uu____83211 =
                       let uu____83213 = is_flex scrutinee  in
                       Prims.op_Negation uu____83213  in
                     if uu____83211
                     then
                       ((let uu____83224 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____83224
                         then
                           let uu____83229 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____83229
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____83248 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____83248
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____83263 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____83263
                           then
                             let uu____83268 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____83270 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____83268 uu____83270
                           else ());
                          (let pat_discriminates uu___613_83295 =
                             match uu___613_83295 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____83311;
                                  FStar_Syntax_Syntax.p = uu____83312;_},FStar_Pervasives_Native.None
                                ,uu____83313) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____83327;
                                  FStar_Syntax_Syntax.p = uu____83328;_},FStar_Pervasives_Native.None
                                ,uu____83329) -> true
                             | uu____83356 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____83459 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____83459 with
                                       | (uu____83461,uu____83462,t') ->
                                           let uu____83480 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____83480 with
                                            | (FullMatch ,uu____83492) ->
                                                true
                                            | (HeadMatch
                                               uu____83506,uu____83507) ->
                                                true
                                            | uu____83522 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____83559 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____83559
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____83570 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____83570 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____83658,uu____83659) ->
                                       branches1
                                   | uu____83804 -> branches  in
                                 let uu____83859 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____83868 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____83868 with
                                        | (p,uu____83872,uu____83873) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _83902  -> FStar_Util.Inr _83902)
                                   uu____83859))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____83932 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____83932 with
                                | (p,uu____83941,e) ->
                                    ((let uu____83960 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____83960
                                      then
                                        let uu____83965 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____83967 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____83965 uu____83967
                                      else ());
                                     (let uu____83972 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _83987  -> FStar_Util.Inr _83987)
                                        uu____83972)))))
                 | ((s,t),(uu____83990,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____83993;
                                         FStar_Syntax_Syntax.vars =
                                           uu____83994;_}))
                     ->
                     let uu____84063 =
                       let uu____84065 = is_flex scrutinee  in
                       Prims.op_Negation uu____84065  in
                     if uu____84063
                     then
                       ((let uu____84076 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____84076
                         then
                           let uu____84081 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____84081
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____84100 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____84100
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____84115 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____84115
                           then
                             let uu____84120 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____84122 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____84120 uu____84122
                           else ());
                          (let pat_discriminates uu___613_84147 =
                             match uu___613_84147 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____84163;
                                  FStar_Syntax_Syntax.p = uu____84164;_},FStar_Pervasives_Native.None
                                ,uu____84165) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____84179;
                                  FStar_Syntax_Syntax.p = uu____84180;_},FStar_Pervasives_Native.None
                                ,uu____84181) -> true
                             | uu____84208 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____84311 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____84311 with
                                       | (uu____84313,uu____84314,t') ->
                                           let uu____84332 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____84332 with
                                            | (FullMatch ,uu____84344) ->
                                                true
                                            | (HeadMatch
                                               uu____84358,uu____84359) ->
                                                true
                                            | uu____84374 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____84411 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____84411
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____84422 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____84422 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____84510,uu____84511) ->
                                       branches1
                                   | uu____84656 -> branches  in
                                 let uu____84711 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____84720 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____84720 with
                                        | (p,uu____84724,uu____84725) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _84754  -> FStar_Util.Inr _84754)
                                   uu____84711))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____84784 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____84784 with
                                | (p,uu____84793,e) ->
                                    ((let uu____84812 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____84812
                                      then
                                        let uu____84817 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____84819 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____84817 uu____84819
                                      else ());
                                     (let uu____84824 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _84839  -> FStar_Util.Inr _84839)
                                        uu____84824)))))
                 | uu____84840 ->
                     ((let uu____84862 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____84862
                       then
                         let uu____84867 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____84869 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____84867 uu____84869
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____84915 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____84915
            then
              let uu____84920 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____84922 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____84924 = FStar_Syntax_Print.term_to_string t1  in
              let uu____84926 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____84920 uu____84922 uu____84924 uu____84926
            else ());
           (let uu____84931 = head_matches_delta env1 wl1 t1 t2  in
            match uu____84931 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____84962,uu____84963) ->
                     let rec may_relate head3 =
                       let uu____84991 =
                         let uu____84992 = FStar_Syntax_Subst.compress head3
                            in
                         uu____84992.FStar_Syntax_Syntax.n  in
                       match uu____84991 with
                       | FStar_Syntax_Syntax.Tm_name uu____84996 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____84998 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____85023 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____85023 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____85025 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____85028
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____85029 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____85032,uu____85033) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____85075) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____85081) ->
                           may_relate t
                       | uu____85086 -> false  in
                     let uu____85088 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____85088 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____85109 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____85109
                          then
                            let uu____85112 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____85112 with
                             | (guard,wl2) ->
                                 let uu____85119 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____85119)
                          else
                            (let uu____85122 =
                               let uu____85124 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____85126 =
                                 let uu____85128 =
                                   let uu____85132 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____85132
                                     (fun x  ->
                                        let uu____85139 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____85139)
                                    in
                                 FStar_Util.dflt "" uu____85128  in
                               let uu____85144 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____85146 =
                                 let uu____85148 =
                                   let uu____85152 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____85152
                                     (fun x  ->
                                        let uu____85159 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____85159)
                                    in
                                 FStar_Util.dflt "" uu____85148  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____85124 uu____85126 uu____85144
                                 uu____85146
                                in
                             giveup env1 uu____85122 orig))
                 | (HeadMatch (true ),uu____85165) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____85180 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____85180 with
                        | (guard,wl2) ->
                            let uu____85187 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____85187)
                     else
                       (let uu____85190 =
                          let uu____85192 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____85194 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____85192 uu____85194
                           in
                        giveup env1 uu____85190 orig)
                 | (uu____85197,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___3401_85211 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___3401_85211.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___3401_85211.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___3401_85211.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___3401_85211.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___3401_85211.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___3401_85211.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___3401_85211.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___3401_85211.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____85238 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____85238
          then
            let uu____85241 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____85241
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____85247 =
                let uu____85250 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____85250  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____85247 t1);
             (let uu____85269 =
                let uu____85272 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____85272  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____85269 t2);
             (let uu____85291 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____85291
              then
                let uu____85295 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____85297 =
                  let uu____85299 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____85301 =
                    let uu____85303 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____85303  in
                  Prims.op_Hat uu____85299 uu____85301  in
                let uu____85306 =
                  let uu____85308 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____85310 =
                    let uu____85312 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____85312  in
                  Prims.op_Hat uu____85308 uu____85310  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____85295 uu____85297 uu____85306
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____85319,uu____85320) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____85344,FStar_Syntax_Syntax.Tm_delayed uu____85345) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____85369,uu____85370) ->
                  let uu____85397 =
                    let uu___3432_85398 = problem  in
                    let uu____85399 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3432_85398.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____85399;
                      FStar_TypeChecker_Common.relation =
                        (uu___3432_85398.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3432_85398.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3432_85398.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3432_85398.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3432_85398.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3432_85398.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3432_85398.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3432_85398.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85397 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____85400,uu____85401) ->
                  let uu____85408 =
                    let uu___3438_85409 = problem  in
                    let uu____85410 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3438_85409.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____85410;
                      FStar_TypeChecker_Common.relation =
                        (uu___3438_85409.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3438_85409.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3438_85409.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3438_85409.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3438_85409.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3438_85409.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3438_85409.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3438_85409.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85408 wl
              | (uu____85411,FStar_Syntax_Syntax.Tm_ascribed uu____85412) ->
                  let uu____85439 =
                    let uu___3444_85440 = problem  in
                    let uu____85441 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3444_85440.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3444_85440.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3444_85440.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____85441;
                      FStar_TypeChecker_Common.element =
                        (uu___3444_85440.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3444_85440.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3444_85440.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3444_85440.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3444_85440.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3444_85440.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85439 wl
              | (uu____85442,FStar_Syntax_Syntax.Tm_meta uu____85443) ->
                  let uu____85450 =
                    let uu___3450_85451 = problem  in
                    let uu____85452 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3450_85451.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3450_85451.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3450_85451.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____85452;
                      FStar_TypeChecker_Common.element =
                        (uu___3450_85451.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3450_85451.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3450_85451.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3450_85451.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3450_85451.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3450_85451.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85450 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____85454),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____85456)) ->
                  let uu____85465 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____85465
              | (FStar_Syntax_Syntax.Tm_bvar uu____85466,uu____85467) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____85469,FStar_Syntax_Syntax.Tm_bvar uu____85470) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___614_85540 =
                    match uu___614_85540 with
                    | [] -> c
                    | bs ->
                        let uu____85568 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____85568
                     in
                  let uu____85579 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____85579 with
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
                                    let uu____85728 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____85728
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
                  let mk_t t l uu___615_85817 =
                    match uu___615_85817 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____85859 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____85859 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____86004 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____86005 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____86004
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____86005 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____86007,uu____86008) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____86039 -> true
                    | uu____86059 -> false  in
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
                      (let uu____86119 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_86127 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_86127.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_86127.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_86127.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_86127.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_86127.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_86127.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_86127.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_86127.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_86127.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_86127.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_86127.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_86127.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_86127.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_86127.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_86127.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_86127.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_86127.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_86127.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_86127.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_86127.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_86127.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_86127.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_86127.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_86127.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_86127.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_86127.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_86127.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_86127.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_86127.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_86127.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_86127.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_86127.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_86127.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_86127.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_86127.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_86127.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_86127.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_86127.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_86127.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_86127.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____86119 with
                       | (uu____86132,ty,uu____86134) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____86143 =
                                 let uu____86144 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____86144.FStar_Syntax_Syntax.n  in
                               match uu____86143 with
                               | FStar_Syntax_Syntax.Tm_refine uu____86147 ->
                                   let uu____86154 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____86154
                               | uu____86155 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____86158 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____86158
                             then
                               let uu____86163 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____86165 =
                                 let uu____86167 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____86167
                                  in
                               let uu____86168 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____86163 uu____86165 uu____86168
                             else ());
                            r1))
                     in
                  let uu____86173 =
                    let uu____86190 = maybe_eta t1  in
                    let uu____86197 = maybe_eta t2  in
                    (uu____86190, uu____86197)  in
                  (match uu____86173 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_86239 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_86239.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_86239.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_86239.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_86239.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_86239.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_86239.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_86239.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_86239.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____86260 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86260
                       then
                         let uu____86263 = destruct_flex_t not_abs wl  in
                         (match uu____86263 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86280 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86280.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86280.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86280.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86280.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86280.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86280.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86280.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86280.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____86304 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86304
                       then
                         let uu____86307 = destruct_flex_t not_abs wl  in
                         (match uu____86307 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86324 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86324.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86324.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86324.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86324.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86324.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86324.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86324.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86324.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____86328 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____86346,FStar_Syntax_Syntax.Tm_abs uu____86347) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____86378 -> true
                    | uu____86398 -> false  in
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
                      (let uu____86458 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_86466 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_86466.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_86466.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_86466.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_86466.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_86466.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_86466.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_86466.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_86466.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_86466.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_86466.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_86466.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_86466.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_86466.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_86466.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_86466.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_86466.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_86466.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_86466.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_86466.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_86466.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_86466.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_86466.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_86466.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_86466.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_86466.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_86466.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_86466.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_86466.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_86466.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_86466.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_86466.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_86466.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_86466.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_86466.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_86466.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_86466.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_86466.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_86466.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_86466.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_86466.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____86458 with
                       | (uu____86471,ty,uu____86473) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____86482 =
                                 let uu____86483 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____86483.FStar_Syntax_Syntax.n  in
                               match uu____86482 with
                               | FStar_Syntax_Syntax.Tm_refine uu____86486 ->
                                   let uu____86493 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____86493
                               | uu____86494 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____86497 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____86497
                             then
                               let uu____86502 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____86504 =
                                 let uu____86506 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____86506
                                  in
                               let uu____86507 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____86502 uu____86504 uu____86507
                             else ());
                            r1))
                     in
                  let uu____86512 =
                    let uu____86529 = maybe_eta t1  in
                    let uu____86536 = maybe_eta t2  in
                    (uu____86529, uu____86536)  in
                  (match uu____86512 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_86578 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_86578.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_86578.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_86578.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_86578.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_86578.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_86578.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_86578.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_86578.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____86599 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86599
                       then
                         let uu____86602 = destruct_flex_t not_abs wl  in
                         (match uu____86602 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86619 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86619.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86619.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86619.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86619.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86619.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86619.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86619.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86619.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____86643 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86643
                       then
                         let uu____86646 = destruct_flex_t not_abs wl  in
                         (match uu____86646 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86663 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86663.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86663.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86663.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86663.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86663.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86663.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86663.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86663.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____86667 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____86697 =
                    let uu____86702 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____86702 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3613_86730 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_86730.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_86730.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_86732 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_86732.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_86732.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____86733,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3613_86748 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_86748.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_86748.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_86750 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_86750.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_86750.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____86751 -> (x1, x2)  in
                  (match uu____86697 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____86770 = as_refinement false env t11  in
                       (match uu____86770 with
                        | (x12,phi11) ->
                            let uu____86778 = as_refinement false env t21  in
                            (match uu____86778 with
                             | (x22,phi21) ->
                                 ((let uu____86787 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____86787
                                   then
                                     ((let uu____86792 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____86794 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86796 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____86792
                                         uu____86794 uu____86796);
                                      (let uu____86799 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____86801 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86803 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____86799
                                         uu____86801 uu____86803))
                                   else ());
                                  (let uu____86808 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____86808 with
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
                                         let uu____86879 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____86879
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____86891 =
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
                                         (let uu____86904 =
                                            let uu____86907 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____86907
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____86904
                                            (p_guard base_prob));
                                         (let uu____86926 =
                                            let uu____86929 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____86929
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____86926
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____86948 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____86948)
                                          in
                                       let has_uvars =
                                         (let uu____86953 =
                                            let uu____86955 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____86955
                                             in
                                          Prims.op_Negation uu____86953) ||
                                           (let uu____86959 =
                                              let uu____86961 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____86961
                                               in
                                            Prims.op_Negation uu____86959)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____86965 =
                                           let uu____86970 =
                                             let uu____86979 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____86979]  in
                                           mk_t_problem wl1 uu____86970 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____86965 with
                                          | (ref_prob,wl2) ->
                                              let uu____87001 =
                                                solve env1
                                                  (let uu___3657_87003 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3657_87003.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3657_87003.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3657_87003.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3657_87003.tcenv);
                                                     wl_implicits =
                                                       (uu___3657_87003.wl_implicits)
                                                   })
                                                 in
                                              (match uu____87001 with
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
                                               | Success uu____87020 ->
                                                   let guard =
                                                     let uu____87028 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____87028
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3668_87037 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3668_87037.attempting);
                                                       wl_deferred =
                                                         (uu___3668_87037.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___3668_87037.defer_ok);
                                                       smt_ok =
                                                         (uu___3668_87037.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3668_87037.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3668_87037.tcenv);
                                                       wl_implicits =
                                                         (uu___3668_87037.wl_implicits)
                                                     }  in
                                                   let uu____87039 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____87039))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87042,FStar_Syntax_Syntax.Tm_uvar uu____87043) ->
                  let uu____87068 = destruct_flex_t t1 wl  in
                  (match uu____87068 with
                   | (f1,wl1) ->
                       let uu____87075 = destruct_flex_t t2 wl1  in
                       (match uu____87075 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87082;
                    FStar_Syntax_Syntax.pos = uu____87083;
                    FStar_Syntax_Syntax.vars = uu____87084;_},uu____87085),FStar_Syntax_Syntax.Tm_uvar
                 uu____87086) ->
                  let uu____87135 = destruct_flex_t t1 wl  in
                  (match uu____87135 with
                   | (f1,wl1) ->
                       let uu____87142 = destruct_flex_t t2 wl1  in
                       (match uu____87142 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87149,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87150;
                    FStar_Syntax_Syntax.pos = uu____87151;
                    FStar_Syntax_Syntax.vars = uu____87152;_},uu____87153))
                  ->
                  let uu____87202 = destruct_flex_t t1 wl  in
                  (match uu____87202 with
                   | (f1,wl1) ->
                       let uu____87209 = destruct_flex_t t2 wl1  in
                       (match uu____87209 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87216;
                    FStar_Syntax_Syntax.pos = uu____87217;
                    FStar_Syntax_Syntax.vars = uu____87218;_},uu____87219),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87220;
                    FStar_Syntax_Syntax.pos = uu____87221;
                    FStar_Syntax_Syntax.vars = uu____87222;_},uu____87223))
                  ->
                  let uu____87296 = destruct_flex_t t1 wl  in
                  (match uu____87296 with
                   | (f1,wl1) ->
                       let uu____87303 = destruct_flex_t t2 wl1  in
                       (match uu____87303 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____87310,uu____87311) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____87324 = destruct_flex_t t1 wl  in
                  (match uu____87324 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87331;
                    FStar_Syntax_Syntax.pos = uu____87332;
                    FStar_Syntax_Syntax.vars = uu____87333;_},uu____87334),uu____87335)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____87372 = destruct_flex_t t1 wl  in
                  (match uu____87372 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____87379,FStar_Syntax_Syntax.Tm_uvar uu____87380) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____87393,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87394;
                    FStar_Syntax_Syntax.pos = uu____87395;
                    FStar_Syntax_Syntax.vars = uu____87396;_},uu____87397))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87434,FStar_Syntax_Syntax.Tm_arrow uu____87435) ->
                  solve_t' env
                    (let uu___3768_87463 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_87463.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_87463.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_87463.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_87463.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_87463.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_87463.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_87463.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_87463.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_87463.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87464;
                    FStar_Syntax_Syntax.pos = uu____87465;
                    FStar_Syntax_Syntax.vars = uu____87466;_},uu____87467),FStar_Syntax_Syntax.Tm_arrow
                 uu____87468) ->
                  solve_t' env
                    (let uu___3768_87520 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_87520.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_87520.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_87520.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_87520.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_87520.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_87520.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_87520.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_87520.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_87520.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____87521,FStar_Syntax_Syntax.Tm_uvar uu____87522) ->
                  let uu____87535 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87535
              | (uu____87536,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87537;
                    FStar_Syntax_Syntax.pos = uu____87538;
                    FStar_Syntax_Syntax.vars = uu____87539;_},uu____87540))
                  ->
                  let uu____87577 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87577
              | (FStar_Syntax_Syntax.Tm_uvar uu____87578,uu____87579) ->
                  let uu____87592 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87592
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87593;
                    FStar_Syntax_Syntax.pos = uu____87594;
                    FStar_Syntax_Syntax.vars = uu____87595;_},uu____87596),uu____87597)
                  ->
                  let uu____87634 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87634
              | (FStar_Syntax_Syntax.Tm_refine uu____87635,uu____87636) ->
                  let t21 =
                    let uu____87644 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____87644  in
                  solve_t env
                    (let uu___3803_87670 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3803_87670.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3803_87670.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3803_87670.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3803_87670.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3803_87670.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3803_87670.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3803_87670.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3803_87670.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3803_87670.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____87671,FStar_Syntax_Syntax.Tm_refine uu____87672) ->
                  let t11 =
                    let uu____87680 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____87680  in
                  solve_t env
                    (let uu___3810_87706 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3810_87706.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3810_87706.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3810_87706.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3810_87706.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3810_87706.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3810_87706.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3810_87706.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3810_87706.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3810_87706.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____87788 =
                    let uu____87789 = guard_of_prob env wl problem t1 t2  in
                    match uu____87789 with
                    | (guard,wl1) ->
                        let uu____87796 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____87796
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____88015 = br1  in
                        (match uu____88015 with
                         | (p1,w1,uu____88044) ->
                             let uu____88061 = br2  in
                             (match uu____88061 with
                              | (p2,w2,uu____88084) ->
                                  let uu____88089 =
                                    let uu____88091 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____88091  in
                                  if uu____88089
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____88118 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____88118 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____88155 = br2  in
                                         (match uu____88155 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____88188 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____88188
                                                 in
                                              let uu____88193 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____88224,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____88245) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____88304 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____88304 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____88193
                                                (fun uu____88376  ->
                                                   match uu____88376 with
                                                   | (wprobs,wl2) ->
                                                       let uu____88413 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____88413
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____88434
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____88434
                                                              then
                                                                let uu____88439
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____88441
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____88439
                                                                  uu____88441
                                                              else ());
                                                             (let uu____88447
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____88447
                                                                (fun
                                                                   uu____88483
                                                                    ->
                                                                   match uu____88483
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
                    | uu____88612 -> FStar_Pervasives_Native.None  in
                  let uu____88653 = solve_branches wl brs1 brs2  in
                  (match uu____88653 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____88704 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____88704 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____88738 =
                                FStar_List.map
                                  (fun uu____88750  ->
                                     match uu____88750 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____88738  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____88759 =
                              let uu____88760 =
                                let uu____88761 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____88761
                                  (let uu___3909_88769 = wl3  in
                                   {
                                     attempting =
                                       (uu___3909_88769.attempting);
                                     wl_deferred =
                                       (uu___3909_88769.wl_deferred);
                                     ctr = (uu___3909_88769.ctr);
                                     defer_ok = (uu___3909_88769.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3909_88769.umax_heuristic_ok);
                                     tcenv = (uu___3909_88769.tcenv);
                                     wl_implicits =
                                       (uu___3909_88769.wl_implicits)
                                   })
                                 in
                              solve env uu____88760  in
                            (match uu____88759 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____88774 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____88781,uu____88782) ->
                  let head1 =
                    let uu____88806 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____88806
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____88852 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____88852
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____88898 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____88898
                    then
                      let uu____88902 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____88904 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____88906 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____88902 uu____88904 uu____88906
                    else ());
                   (let no_free_uvars t =
                      (let uu____88920 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____88920) &&
                        (let uu____88924 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____88924)
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
                      let uu____88941 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____88941 = FStar_Syntax_Util.Equal  in
                    let uu____88942 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____88942
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____88946 = equal t1 t2  in
                         (if uu____88946
                          then
                            let uu____88949 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____88949
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____88954 =
                            let uu____88961 = equal t1 t2  in
                            if uu____88961
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____88974 = mk_eq2 wl env orig t1 t2  in
                               match uu____88974 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____88954 with
                          | (guard,wl1) ->
                              let uu____88995 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____88995))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____88998,uu____88999) ->
                  let head1 =
                    let uu____89007 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89007
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89053 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89053
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89099 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89099
                    then
                      let uu____89103 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89105 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89107 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89103 uu____89105 uu____89107
                    else ());
                   (let no_free_uvars t =
                      (let uu____89121 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89121) &&
                        (let uu____89125 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89125)
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
                      let uu____89142 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89142 = FStar_Syntax_Util.Equal  in
                    let uu____89143 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89143
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89147 = equal t1 t2  in
                         (if uu____89147
                          then
                            let uu____89150 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89150
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89155 =
                            let uu____89162 = equal t1 t2  in
                            if uu____89162
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89175 = mk_eq2 wl env orig t1 t2  in
                               match uu____89175 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89155 with
                          | (guard,wl1) ->
                              let uu____89196 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89196))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____89199,uu____89200) ->
                  let head1 =
                    let uu____89202 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89202
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89248 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89248
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89294 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89294
                    then
                      let uu____89298 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89300 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89302 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89298 uu____89300 uu____89302
                    else ());
                   (let no_free_uvars t =
                      (let uu____89316 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89316) &&
                        (let uu____89320 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89320)
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
                      let uu____89337 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89337 = FStar_Syntax_Util.Equal  in
                    let uu____89338 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89338
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89342 = equal t1 t2  in
                         (if uu____89342
                          then
                            let uu____89345 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89345
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89350 =
                            let uu____89357 = equal t1 t2  in
                            if uu____89357
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89370 = mk_eq2 wl env orig t1 t2  in
                               match uu____89370 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89350 with
                          | (guard,wl1) ->
                              let uu____89391 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89391))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____89394,uu____89395) ->
                  let head1 =
                    let uu____89397 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89397
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89443 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89443
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89489 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89489
                    then
                      let uu____89493 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89495 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89497 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89493 uu____89495 uu____89497
                    else ());
                   (let no_free_uvars t =
                      (let uu____89511 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89511) &&
                        (let uu____89515 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89515)
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
                      let uu____89532 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89532 = FStar_Syntax_Util.Equal  in
                    let uu____89533 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89533
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89537 = equal t1 t2  in
                         (if uu____89537
                          then
                            let uu____89540 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89540
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89545 =
                            let uu____89552 = equal t1 t2  in
                            if uu____89552
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89565 = mk_eq2 wl env orig t1 t2  in
                               match uu____89565 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89545 with
                          | (guard,wl1) ->
                              let uu____89586 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89586))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____89589,uu____89590) ->
                  let head1 =
                    let uu____89592 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89592
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89638 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89638
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89684 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89684
                    then
                      let uu____89688 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89690 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89692 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89688 uu____89690 uu____89692
                    else ());
                   (let no_free_uvars t =
                      (let uu____89706 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89706) &&
                        (let uu____89710 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89710)
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
                      let uu____89727 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89727 = FStar_Syntax_Util.Equal  in
                    let uu____89728 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89728
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89732 = equal t1 t2  in
                         (if uu____89732
                          then
                            let uu____89735 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89735
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89740 =
                            let uu____89747 = equal t1 t2  in
                            if uu____89747
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89760 = mk_eq2 wl env orig t1 t2  in
                               match uu____89760 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89740 with
                          | (guard,wl1) ->
                              let uu____89781 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89781))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____89784,uu____89785) ->
                  let head1 =
                    let uu____89803 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89803
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89849 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89849
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89895 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89895
                    then
                      let uu____89899 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89901 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89903 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89899 uu____89901 uu____89903
                    else ());
                   (let no_free_uvars t =
                      (let uu____89917 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89917) &&
                        (let uu____89921 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89921)
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
                      let uu____89938 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89938 = FStar_Syntax_Util.Equal  in
                    let uu____89939 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89939
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89943 = equal t1 t2  in
                         (if uu____89943
                          then
                            let uu____89946 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89946
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89951 =
                            let uu____89958 = equal t1 t2  in
                            if uu____89958
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89971 = mk_eq2 wl env orig t1 t2  in
                               match uu____89971 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89951 with
                          | (guard,wl1) ->
                              let uu____89992 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89992))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____89995,FStar_Syntax_Syntax.Tm_match uu____89996) ->
                  let head1 =
                    let uu____90020 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90020
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90066 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90066
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90112 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90112
                    then
                      let uu____90116 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90118 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90120 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90116 uu____90118 uu____90120
                    else ());
                   (let no_free_uvars t =
                      (let uu____90134 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90134) &&
                        (let uu____90138 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90138)
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
                      let uu____90155 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90155 = FStar_Syntax_Util.Equal  in
                    let uu____90156 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90156
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90160 = equal t1 t2  in
                         (if uu____90160
                          then
                            let uu____90163 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90163
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90168 =
                            let uu____90175 = equal t1 t2  in
                            if uu____90175
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90188 = mk_eq2 wl env orig t1 t2  in
                               match uu____90188 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90168 with
                          | (guard,wl1) ->
                              let uu____90209 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90209))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90212,FStar_Syntax_Syntax.Tm_uinst uu____90213) ->
                  let head1 =
                    let uu____90221 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90221
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90261 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90261
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90301 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90301
                    then
                      let uu____90305 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90307 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90309 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90305 uu____90307 uu____90309
                    else ());
                   (let no_free_uvars t =
                      (let uu____90323 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90323) &&
                        (let uu____90327 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90327)
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
                      let uu____90344 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90344 = FStar_Syntax_Util.Equal  in
                    let uu____90345 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90345
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90349 = equal t1 t2  in
                         (if uu____90349
                          then
                            let uu____90352 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90352
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90357 =
                            let uu____90364 = equal t1 t2  in
                            if uu____90364
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90377 = mk_eq2 wl env orig t1 t2  in
                               match uu____90377 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90357 with
                          | (guard,wl1) ->
                              let uu____90398 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90398))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90401,FStar_Syntax_Syntax.Tm_name uu____90402) ->
                  let head1 =
                    let uu____90404 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90404
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90444 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90444
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90484 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90484
                    then
                      let uu____90488 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90490 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90492 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90488 uu____90490 uu____90492
                    else ());
                   (let no_free_uvars t =
                      (let uu____90506 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90506) &&
                        (let uu____90510 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90510)
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
                      let uu____90527 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90527 = FStar_Syntax_Util.Equal  in
                    let uu____90528 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90528
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90532 = equal t1 t2  in
                         (if uu____90532
                          then
                            let uu____90535 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90535
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90540 =
                            let uu____90547 = equal t1 t2  in
                            if uu____90547
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90560 = mk_eq2 wl env orig t1 t2  in
                               match uu____90560 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90540 with
                          | (guard,wl1) ->
                              let uu____90581 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90581))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90584,FStar_Syntax_Syntax.Tm_constant uu____90585) ->
                  let head1 =
                    let uu____90587 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90587
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90627 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90627
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90667 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90667
                    then
                      let uu____90671 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90673 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90675 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90671 uu____90673 uu____90675
                    else ());
                   (let no_free_uvars t =
                      (let uu____90689 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90689) &&
                        (let uu____90693 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90693)
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
                      let uu____90710 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90710 = FStar_Syntax_Util.Equal  in
                    let uu____90711 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90711
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90715 = equal t1 t2  in
                         (if uu____90715
                          then
                            let uu____90718 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90718
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90723 =
                            let uu____90730 = equal t1 t2  in
                            if uu____90730
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90743 = mk_eq2 wl env orig t1 t2  in
                               match uu____90743 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90723 with
                          | (guard,wl1) ->
                              let uu____90764 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90764))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90767,FStar_Syntax_Syntax.Tm_fvar uu____90768) ->
                  let head1 =
                    let uu____90770 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90770
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90810 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90810
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90850 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90850
                    then
                      let uu____90854 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90856 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90858 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90854 uu____90856 uu____90858
                    else ());
                   (let no_free_uvars t =
                      (let uu____90872 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90872) &&
                        (let uu____90876 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90876)
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
                      let uu____90893 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90893 = FStar_Syntax_Util.Equal  in
                    let uu____90894 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90894
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90898 = equal t1 t2  in
                         (if uu____90898
                          then
                            let uu____90901 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90901
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90906 =
                            let uu____90913 = equal t1 t2  in
                            if uu____90913
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90926 = mk_eq2 wl env orig t1 t2  in
                               match uu____90926 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90906 with
                          | (guard,wl1) ->
                              let uu____90947 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90947))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90950,FStar_Syntax_Syntax.Tm_app uu____90951) ->
                  let head1 =
                    let uu____90969 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90969
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____91009 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____91009
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____91049 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____91049
                    then
                      let uu____91053 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____91055 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____91057 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____91053 uu____91055 uu____91057
                    else ());
                   (let no_free_uvars t =
                      (let uu____91071 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____91071) &&
                        (let uu____91075 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____91075)
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
                      let uu____91092 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____91092 = FStar_Syntax_Util.Equal  in
                    let uu____91093 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____91093
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____91097 = equal t1 t2  in
                         (if uu____91097
                          then
                            let uu____91100 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____91100
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____91105 =
                            let uu____91112 = equal t1 t2  in
                            if uu____91112
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____91125 = mk_eq2 wl env orig t1 t2  in
                               match uu____91125 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____91105 with
                          | (guard,wl1) ->
                              let uu____91146 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____91146))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____91149,FStar_Syntax_Syntax.Tm_let uu____91150) ->
                  let uu____91177 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____91177
                  then
                    let uu____91180 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____91180
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____91184,uu____91185) ->
                  let uu____91199 =
                    let uu____91205 =
                      let uu____91207 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____91209 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____91211 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____91213 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____91207 uu____91209 uu____91211 uu____91213
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____91205)
                     in
                  FStar_Errors.raise_error uu____91199
                    t1.FStar_Syntax_Syntax.pos
              | (uu____91217,FStar_Syntax_Syntax.Tm_let uu____91218) ->
                  let uu____91232 =
                    let uu____91238 =
                      let uu____91240 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____91242 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____91244 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____91246 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____91240 uu____91242 uu____91244 uu____91246
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____91238)
                     in
                  FStar_Errors.raise_error uu____91232
                    t1.FStar_Syntax_Syntax.pos
              | uu____91250 -> giveup env "head tag mismatch" orig))))

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
          (let uu____91314 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____91314
           then
             let uu____91319 =
               let uu____91321 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____91321  in
             let uu____91322 =
               let uu____91324 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____91324  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____91319 uu____91322
           else ());
          (let uu____91328 =
             let uu____91330 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____91330  in
           if uu____91328
           then
             let uu____91333 =
               let uu____91335 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____91337 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____91335 uu____91337
                in
             giveup env uu____91333 orig
           else
             (let uu____91342 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____91342 with
              | (ret_sub_prob,wl1) ->
                  let uu____91350 =
                    FStar_List.fold_right2
                      (fun uu____91387  ->
                         fun uu____91388  ->
                           fun uu____91389  ->
                             match (uu____91387, uu____91388, uu____91389)
                             with
                             | ((a1,uu____91433),(a2,uu____91435),(arg_sub_probs,wl2))
                                 ->
                                 let uu____91468 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____91468 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____91350 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____91498 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____91498  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____91506 = attempt sub_probs wl3  in
                       solve env uu____91506)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____91529 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____91532)::[] -> wp1
              | uu____91557 ->
                  let uu____91568 =
                    let uu____91570 =
                      let uu____91572 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____91572  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____91570
                     in
                  failwith uu____91568
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____91579 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____91579]
              | x -> x  in
            let uu____91581 =
              let uu____91592 =
                let uu____91601 =
                  let uu____91602 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____91602 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____91601  in
              [uu____91592]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____91581;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____91620 = lift_c1 ()  in solve_eq uu____91620 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___616_91629  ->
                       match uu___616_91629 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____91634 -> false))
                in
             let uu____91636 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____91666)::uu____91667,(wp2,uu____91669)::uu____91670)
                   -> (wp1, wp2)
               | uu____91743 ->
                   let uu____91768 =
                     let uu____91774 =
                       let uu____91776 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____91778 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____91776 uu____91778
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____91774)
                      in
                   FStar_Errors.raise_error uu____91768
                     env.FStar_TypeChecker_Env.range
                in
             match uu____91636 with
             | (wpc1,wpc2) ->
                 let uu____91788 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____91788
                 then
                   let uu____91793 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____91793 wl
                 else
                   (let uu____91797 =
                      let uu____91804 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____91804  in
                    match uu____91797 with
                    | (c2_decl,qualifiers) ->
                        let uu____91825 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____91825
                        then
                          let c1_repr =
                            let uu____91832 =
                              let uu____91833 =
                                let uu____91834 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____91834  in
                              let uu____91835 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____91833 uu____91835
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____91832
                             in
                          let c2_repr =
                            let uu____91837 =
                              let uu____91838 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____91839 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____91838 uu____91839
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____91837
                             in
                          let uu____91840 =
                            let uu____91845 =
                              let uu____91847 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____91849 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____91847 uu____91849
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____91845
                             in
                          (match uu____91840 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____91855 = attempt [prob] wl2  in
                               solve env uu____91855)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____91870 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____91870
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____91879 =
                                     let uu____91886 =
                                       let uu____91887 =
                                         let uu____91904 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____91907 =
                                           let uu____91918 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____91927 =
                                             let uu____91938 =
                                               let uu____91947 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____91947
                                                in
                                             [uu____91938]  in
                                           uu____91918 :: uu____91927  in
                                         (uu____91904, uu____91907)  in
                                       FStar_Syntax_Syntax.Tm_app uu____91887
                                        in
                                     FStar_Syntax_Syntax.mk uu____91886  in
                                   uu____91879 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____91999 =
                                    let uu____92006 =
                                      let uu____92007 =
                                        let uu____92024 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____92027 =
                                          let uu____92038 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____92047 =
                                            let uu____92058 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____92067 =
                                              let uu____92078 =
                                                let uu____92087 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____92087
                                                 in
                                              [uu____92078]  in
                                            uu____92058 :: uu____92067  in
                                          uu____92038 :: uu____92047  in
                                        (uu____92024, uu____92027)  in
                                      FStar_Syntax_Syntax.Tm_app uu____92007
                                       in
                                    FStar_Syntax_Syntax.mk uu____92006  in
                                  uu____91999 FStar_Pervasives_Native.None r)
                              in
                           (let uu____92144 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____92144
                            then
                              let uu____92149 =
                                let uu____92151 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____92151
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____92149
                            else ());
                           (let uu____92155 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____92155 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____92164 =
                                    let uu____92167 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _92170  ->
                                         FStar_Pervasives_Native.Some _92170)
                                      uu____92167
                                     in
                                  solve_prob orig uu____92164 [] wl1  in
                                let uu____92171 = attempt [base_prob] wl2  in
                                solve env uu____92171))))
           in
        let uu____92172 = FStar_Util.physical_equality c1 c2  in
        if uu____92172
        then
          let uu____92175 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____92175
        else
          ((let uu____92179 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____92179
            then
              let uu____92184 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____92186 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____92184
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____92186
            else ());
           (let uu____92191 =
              let uu____92200 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____92203 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____92200, uu____92203)  in
            match uu____92191 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____92221),FStar_Syntax_Syntax.Total
                    (t2,uu____92223)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____92240 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92240 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____92242,FStar_Syntax_Syntax.Total uu____92243) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____92262),FStar_Syntax_Syntax.Total
                    (t2,uu____92264)) ->
                     let uu____92281 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92281 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____92284),FStar_Syntax_Syntax.GTotal
                    (t2,uu____92286)) ->
                     let uu____92303 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92303 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____92306),FStar_Syntax_Syntax.GTotal
                    (t2,uu____92308)) ->
                     let uu____92325 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92325 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____92327,FStar_Syntax_Syntax.Comp uu____92328) ->
                     let uu____92337 =
                       let uu___4158_92340 = problem  in
                       let uu____92343 =
                         let uu____92344 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92344
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_92340.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____92343;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_92340.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_92340.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_92340.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_92340.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_92340.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_92340.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_92340.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_92340.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92337 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____92345,FStar_Syntax_Syntax.Comp uu____92346) ->
                     let uu____92355 =
                       let uu___4158_92358 = problem  in
                       let uu____92361 =
                         let uu____92362 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92362
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_92358.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____92361;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_92358.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_92358.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_92358.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_92358.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_92358.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_92358.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_92358.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_92358.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92355 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92363,FStar_Syntax_Syntax.GTotal uu____92364) ->
                     let uu____92373 =
                       let uu___4170_92376 = problem  in
                       let uu____92379 =
                         let uu____92380 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92380
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_92376.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_92376.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_92376.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____92379;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_92376.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_92376.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_92376.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_92376.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_92376.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_92376.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92373 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92381,FStar_Syntax_Syntax.Total uu____92382) ->
                     let uu____92391 =
                       let uu___4170_92394 = problem  in
                       let uu____92397 =
                         let uu____92398 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92398
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_92394.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_92394.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_92394.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____92397;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_92394.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_92394.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_92394.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_92394.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_92394.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_92394.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92391 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92399,FStar_Syntax_Syntax.Comp uu____92400) ->
                     let uu____92401 =
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
                     if uu____92401
                     then
                       let uu____92404 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____92404 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____92411 =
                            let uu____92416 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____92416
                            then (c1_comp, c2_comp)
                            else
                              (let uu____92425 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____92426 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____92425, uu____92426))
                             in
                          match uu____92411 with
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
                           (let uu____92434 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____92434
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____92442 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____92442 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____92445 =
                                  let uu____92447 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____92449 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____92447 uu____92449
                                   in
                                giveup env uu____92445 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____92460 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____92460 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____92510 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____92510 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____92535 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____92566  ->
                match uu____92566 with
                | (u1,u2) ->
                    let uu____92574 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____92576 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____92574 uu____92576))
         in
      FStar_All.pipe_right uu____92535 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____92613,[])) when
          let uu____92640 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____92640 -> "{}"
      | uu____92643 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____92670 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____92670
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____92682 =
              FStar_List.map
                (fun uu____92695  ->
                   match uu____92695 with
                   | (uu____92702,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____92682 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____92713 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____92713 imps
  
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
                  let uu____92770 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____92770
                  then
                    let uu____92778 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____92780 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____92778
                      (rel_to_string rel) uu____92780
                  else "TOP"  in
                let uu____92786 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____92786 with
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
              let uu____92846 =
                let uu____92849 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _92852  -> FStar_Pervasives_Native.Some _92852)
                  uu____92849
                 in
              FStar_Syntax_Syntax.new_bv uu____92846 t1  in
            let uu____92853 =
              let uu____92858 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____92858
               in
            match uu____92853 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____92918 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____92918
         then
           let uu____92923 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____92923
         else ());
        (let uu____92930 =
           FStar_Util.record_time (fun uu____92937  -> solve env probs)  in
         match uu____92930 with
         | (sol,ms) ->
             ((let uu____92949 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____92949
               then
                 let uu____92954 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____92954
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____92967 =
                     FStar_Util.record_time
                       (fun uu____92974  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____92967 with
                    | ((),ms1) ->
                        ((let uu____92985 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____92985
                          then
                            let uu____92990 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____92990
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____93004 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____93004
                     then
                       let uu____93011 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____93011
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
          ((let uu____93038 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____93038
            then
              let uu____93043 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____93043
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____93050 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____93050
             then
               let uu____93055 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____93055
             else ());
            (let f2 =
               let uu____93061 =
                 let uu____93062 = FStar_Syntax_Util.unmeta f1  in
                 uu____93062.FStar_Syntax_Syntax.n  in
               match uu____93061 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____93066 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4286_93067 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___4286_93067.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___4286_93067.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___4286_93067.FStar_TypeChecker_Env.implicits)
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
            let uu____93122 =
              let uu____93123 =
                let uu____93124 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _93125  ->
                       FStar_TypeChecker_Common.NonTrivial _93125)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____93124;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____93123  in
            FStar_All.pipe_left
              (fun _93132  -> FStar_Pervasives_Native.Some _93132)
              uu____93122
  
let with_guard_no_simp :
  'Auu____93142 .
    'Auu____93142 ->
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
            let uu____93165 =
              let uu____93166 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _93167  -> FStar_TypeChecker_Common.NonTrivial _93167)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____93166;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____93165
  
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
          (let uu____93200 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____93200
           then
             let uu____93205 = FStar_Syntax_Print.term_to_string t1  in
             let uu____93207 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____93205
               uu____93207
           else ());
          (let uu____93212 =
             let uu____93217 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____93217
              in
           match uu____93212 with
           | (prob,wl) ->
               let g =
                 let uu____93225 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____93235  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____93225  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____93271 = try_teq true env t1 t2  in
        match uu____93271 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____93276 = FStar_TypeChecker_Env.get_range env  in
              let uu____93277 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____93276 uu____93277);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____93285 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____93285
              then
                let uu____93290 = FStar_Syntax_Print.term_to_string t1  in
                let uu____93292 = FStar_Syntax_Print.term_to_string t2  in
                let uu____93294 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____93290
                  uu____93292 uu____93294
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
          let uu____93320 = FStar_TypeChecker_Env.get_range env  in
          let uu____93321 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____93320 uu____93321
  
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
        (let uu____93350 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____93350
         then
           let uu____93355 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____93357 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____93355 uu____93357
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____93368 =
           let uu____93375 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____93375 "sub_comp"
            in
         match uu____93368 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____93388 =
                 FStar_Util.record_time
                   (fun uu____93400  ->
                      let uu____93401 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____93412  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____93401)
                  in
               match uu____93388 with
               | (r,ms) ->
                   ((let uu____93443 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____93443
                     then
                       let uu____93448 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____93450 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____93452 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____93448 uu____93450
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____93452
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
      fun uu____93490  ->
        match uu____93490 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____93533 =
                 let uu____93539 =
                   let uu____93541 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____93543 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____93541 uu____93543
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____93539)  in
               let uu____93547 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____93533 uu____93547)
               in
            let equiv1 v1 v' =
              let uu____93560 =
                let uu____93565 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____93566 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____93565, uu____93566)  in
              match uu____93560 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____93586 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____93617 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____93617 with
                      | FStar_Syntax_Syntax.U_unif uu____93624 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____93653  ->
                                    match uu____93653 with
                                    | (u,v') ->
                                        let uu____93662 = equiv1 v1 v'  in
                                        if uu____93662
                                        then
                                          let uu____93667 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____93667 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____93688 -> []))
               in
            let uu____93693 =
              let wl =
                let uu___4377_93697 = empty_worklist env  in
                {
                  attempting = (uu___4377_93697.attempting);
                  wl_deferred = (uu___4377_93697.wl_deferred);
                  ctr = (uu___4377_93697.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4377_93697.smt_ok);
                  umax_heuristic_ok = (uu___4377_93697.umax_heuristic_ok);
                  tcenv = (uu___4377_93697.tcenv);
                  wl_implicits = (uu___4377_93697.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____93716  ->
                      match uu____93716 with
                      | (lb,v1) ->
                          let uu____93723 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____93723 with
                           | USolved wl1 -> ()
                           | uu____93726 -> fail1 lb v1)))
               in
            let rec check_ineq uu____93737 =
              match uu____93737 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____93749) -> true
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
                      uu____93773,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____93775,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____93786) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____93794,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____93803 -> false)
               in
            let uu____93809 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____93826  ->
                      match uu____93826 with
                      | (u,v1) ->
                          let uu____93834 = check_ineq (u, v1)  in
                          if uu____93834
                          then true
                          else
                            ((let uu____93842 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____93842
                              then
                                let uu____93847 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____93849 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____93847
                                  uu____93849
                              else ());
                             false)))
               in
            if uu____93809
            then ()
            else
              ((let uu____93859 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____93859
                then
                  ((let uu____93865 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____93865);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____93877 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____93877))
                else ());
               (let uu____93890 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____93890))
  
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
        let fail1 uu____93964 =
          match uu____93964 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4454_93990 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___4454_93990.attempting);
            wl_deferred = (uu___4454_93990.wl_deferred);
            ctr = (uu___4454_93990.ctr);
            defer_ok;
            smt_ok = (uu___4454_93990.smt_ok);
            umax_heuristic_ok = (uu___4454_93990.umax_heuristic_ok);
            tcenv = (uu___4454_93990.tcenv);
            wl_implicits = (uu___4454_93990.wl_implicits)
          }  in
        (let uu____93993 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____93993
         then
           let uu____93998 = FStar_Util.string_of_bool defer_ok  in
           let uu____94000 = wl_to_string wl  in
           let uu____94002 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____93998 uu____94000 uu____94002
         else ());
        (let g1 =
           let uu____94008 = solve_and_commit env wl fail1  in
           match uu____94008 with
           | FStar_Pervasives_Native.Some
               (uu____94015::uu____94016,uu____94017) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4469_94046 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___4469_94046.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___4469_94046.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____94047 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___4474_94056 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4474_94056.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4474_94056.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___4474_94056.FStar_TypeChecker_Env.implicits)
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
    let uu____94110 = FStar_ST.op_Bang last_proof_ns  in
    match uu____94110 with
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
            let uu___4493_94235 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___4493_94235.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___4493_94235.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___4493_94235.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____94236 =
            let uu____94238 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____94238  in
          if uu____94236
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____94250 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____94251 =
                       let uu____94253 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____94253
                        in
                     FStar_Errors.diag uu____94250 uu____94251)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____94261 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____94262 =
                        let uu____94264 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____94264
                         in
                      FStar_Errors.diag uu____94261 uu____94262)
                   else ();
                   (let uu____94270 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____94270
                      "discharge_guard'" env vc1);
                   (let uu____94272 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____94272 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____94281 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____94282 =
                                let uu____94284 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____94284
                                 in
                              FStar_Errors.diag uu____94281 uu____94282)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____94294 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____94295 =
                                let uu____94297 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____94297
                                 in
                              FStar_Errors.diag uu____94294 uu____94295)
                           else ();
                           (let vcs =
                              let uu____94311 = FStar_Options.use_tactics ()
                                 in
                              if uu____94311
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____94333  ->
                                     (let uu____94335 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____94335);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____94379  ->
                                              match uu____94379 with
                                              | (env1,goal,opts) ->
                                                  let uu____94395 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____94395, opts)))))
                              else
                                (let uu____94398 =
                                   let uu____94405 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____94405)  in
                                 [uu____94398])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____94438  ->
                                    match uu____94438 with
                                    | (env1,goal,opts) ->
                                        let uu____94448 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____94448 with
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
                                                (let uu____94460 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____94461 =
                                                   let uu____94463 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____94465 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____94463 uu____94465
                                                    in
                                                 FStar_Errors.diag
                                                   uu____94460 uu____94461)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____94472 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____94473 =
                                                   let uu____94475 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____94475
                                                    in
                                                 FStar_Errors.diag
                                                   uu____94472 uu____94473)
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
      let uu____94493 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____94493 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____94502 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____94502
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____94516 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____94516 with
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
        let uu____94546 = try_teq false env t1 t2  in
        match uu____94546 with
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
            let uu____94590 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____94590 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____94603 ->
                     let uu____94616 =
                       let uu____94617 = FStar_Syntax_Subst.compress r  in
                       uu____94617.FStar_Syntax_Syntax.n  in
                     (match uu____94616 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____94622) ->
                          unresolved ctx_u'
                      | uu____94639 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____94663 = acc  in
            match uu____94663 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____94682 = hd1  in
                     (match uu____94682 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____94693 = unresolved ctx_u  in
                             if uu____94693
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____94717 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____94717
                                     then
                                       let uu____94721 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____94721
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____94730 = teq_nosmt env1 t tm
                                          in
                                       match uu____94730 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4606_94740 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4606_94740.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4606_94740.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4606_94740.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4606_94740.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4606_94740.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4606_94740.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4606_94740.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4609_94748 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4609_94748.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4609_94748.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4609_94748.FStar_TypeChecker_Env.imp_range)
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
                                    let uu___4613_94759 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4613_94759.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4613_94759.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4613_94759.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4613_94759.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4613_94759.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4613_94759.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4613_94759.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4613_94759.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4613_94759.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4613_94759.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4613_94759.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4613_94759.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4613_94759.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4613_94759.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4613_94759.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4613_94759.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4613_94759.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4613_94759.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4613_94759.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4613_94759.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4613_94759.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4613_94759.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4613_94759.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4613_94759.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4613_94759.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4613_94759.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4613_94759.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4613_94759.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4613_94759.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4613_94759.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4613_94759.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4613_94759.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4613_94759.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4613_94759.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4613_94759.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4613_94759.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4613_94759.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4613_94759.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4613_94759.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4613_94759.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4613_94759.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4613_94759.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4618_94763 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4618_94763.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4618_94763.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4618_94763.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4618_94763.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4618_94763.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4618_94763.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4618_94763.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4618_94763.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4618_94763.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4618_94763.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4618_94763.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4618_94763.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4618_94763.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4618_94763.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4618_94763.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4618_94763.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4618_94763.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4618_94763.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4618_94763.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4618_94763.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4618_94763.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4618_94763.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4618_94763.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4618_94763.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4618_94763.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4618_94763.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4618_94763.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4618_94763.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4618_94763.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4618_94763.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4618_94763.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4618_94763.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4618_94763.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4618_94763.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4618_94763.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4618_94763.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4618_94763.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4618_94763.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4618_94763.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4618_94763.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4618_94763.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4618_94763.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____94768 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____94768
                                   then
                                     let uu____94773 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____94775 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____94777 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____94779 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____94773 uu____94775 uu____94777
                                       reason uu____94779
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4624_94786  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____94793 =
                                             let uu____94803 =
                                               let uu____94811 =
                                                 let uu____94813 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____94815 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____94817 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____94813 uu____94815
                                                   uu____94817
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____94811, r)
                                                in
                                             [uu____94803]  in
                                           FStar_Errors.add_errors
                                             uu____94793);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4632_94837 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4632_94837.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4632_94837.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4632_94837.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____94841 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____94852  ->
                                               let uu____94853 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____94855 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____94857 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____94853 uu____94855
                                                 reason uu____94857)) env2 g2
                                         true
                                        in
                                     match uu____94841 with
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
          let uu___4640_94865 = g  in
          let uu____94866 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4640_94865.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4640_94865.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4640_94865.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____94866
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
        let uu____94909 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____94909 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____94910 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____94910
      | imp::uu____94912 ->
          let uu____94915 =
            let uu____94921 =
              let uu____94923 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____94925 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____94923 uu____94925 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____94921)
             in
          FStar_Errors.raise_error uu____94915
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____94947 = teq_nosmt env t1 t2  in
        match uu____94947 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4662_94966 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4662_94966.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4662_94966.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4662_94966.FStar_TypeChecker_Env.implicits)
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
        (let uu____95002 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____95002
         then
           let uu____95007 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____95009 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____95007
             uu____95009
         else ());
        (let uu____95014 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____95014 with
         | (prob,x,wl) ->
             let g =
               let uu____95033 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____95044  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____95033  in
             ((let uu____95065 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____95065
               then
                 let uu____95070 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____95072 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____95074 =
                   let uu____95076 = FStar_Util.must g  in
                   guard_to_string env uu____95076  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____95070 uu____95072 uu____95074
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
        let uu____95113 = check_subtyping env t1 t2  in
        match uu____95113 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____95132 =
              let uu____95133 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____95133 g  in
            FStar_Pervasives_Native.Some uu____95132
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95152 = check_subtyping env t1 t2  in
        match uu____95152 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____95171 =
              let uu____95172 =
                let uu____95173 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____95173]  in
              FStar_TypeChecker_Env.close_guard env uu____95172 g  in
            FStar_Pervasives_Native.Some uu____95171
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____95211 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____95211
         then
           let uu____95216 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____95218 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____95216
             uu____95218
         else ());
        (let uu____95223 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____95223 with
         | (prob,x,wl) ->
             let g =
               let uu____95238 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____95249  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____95238  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____95273 =
                      let uu____95274 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____95274]  in
                    FStar_TypeChecker_Env.close_guard env uu____95273 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95315 = subtype_nosmt env t1 t2  in
        match uu____95315 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  