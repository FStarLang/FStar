open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____61035 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____61071 -> false
  
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
                    let uu____61495 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____61495;
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
                     (let uu___656_61527 = wl  in
                      {
                        attempting = (uu___656_61527.attempting);
                        wl_deferred = (uu___656_61527.wl_deferred);
                        ctr = (uu___656_61527.ctr);
                        defer_ok = (uu___656_61527.defer_ok);
                        smt_ok = (uu___656_61527.smt_ok);
                        umax_heuristic_ok =
                          (uu___656_61527.umax_heuristic_ok);
                        tcenv = (uu___656_61527.tcenv);
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
            let uu___662_61560 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___662_61560.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___662_61560.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___662_61560.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___662_61560.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___662_61560.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___662_61560.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___662_61560.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___662_61560.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___662_61560.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___662_61560.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___662_61560.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___662_61560.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___662_61560.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___662_61560.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___662_61560.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___662_61560.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___662_61560.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___662_61560.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___662_61560.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___662_61560.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___662_61560.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___662_61560.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___662_61560.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___662_61560.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___662_61560.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___662_61560.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___662_61560.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___662_61560.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___662_61560.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___662_61560.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___662_61560.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___662_61560.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___662_61560.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___662_61560.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___662_61560.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___662_61560.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___662_61560.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___662_61560.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___662_61560.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___662_61560.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___662_61560.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___662_61560.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____61562 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____61562 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____61605 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____61642 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____61676 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____61687 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____61698 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___585_61716  ->
    match uu___585_61716 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____61728 = FStar_Syntax_Util.head_and_args t  in
    match uu____61728 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____61791 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____61793 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____61808 =
                     let uu____61810 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____61810  in
                   FStar_Util.format1 "@<%s>" uu____61808
                in
             let uu____61814 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____61791 uu____61793 uu____61814
         | uu____61817 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___586_61829  ->
      match uu___586_61829 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____61834 =
            let uu____61838 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____61840 =
              let uu____61844 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____61846 =
                let uu____61850 =
                  let uu____61854 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____61854]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____61850
                 in
              uu____61844 :: uu____61846  in
            uu____61838 :: uu____61840  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____61834
      | FStar_TypeChecker_Common.CProb p ->
          let uu____61865 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____61867 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____61869 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____61865
            uu____61867 (rel_to_string p.FStar_TypeChecker_Common.relation)
            uu____61869
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___587_61883  ->
      match uu___587_61883 with
      | UNIV (u,t) ->
          let x =
            let uu____61889 = FStar_Options.hide_uvar_nums ()  in
            if uu____61889
            then "?"
            else
              (let uu____61896 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____61896 FStar_Util.string_of_int)
             in
          let uu____61900 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____61900
      | TERM (u,t) ->
          let x =
            let uu____61907 = FStar_Options.hide_uvar_nums ()  in
            if uu____61907
            then "?"
            else
              (let uu____61914 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____61914 FStar_Util.string_of_int)
             in
          let uu____61918 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____61918
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____61937 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____61937 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____61958 =
      let uu____61962 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____61962
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____61958 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____61981 .
    (FStar_Syntax_Syntax.term * 'Auu____61981) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____62000 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____62021  ->
              match uu____62021 with
              | (x,uu____62028) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____62000 (FStar_String.concat " ")
  
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
        (let uu____62071 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____62071
         then
           let uu____62076 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____62076
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___588_62087  ->
    match uu___588_62087 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____62093 .
    'Auu____62093 FStar_TypeChecker_Common.problem ->
      'Auu____62093 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___722_62105 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___722_62105.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___722_62105.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___722_62105.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___722_62105.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___722_62105.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___722_62105.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___722_62105.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____62113 .
    'Auu____62113 FStar_TypeChecker_Common.problem ->
      'Auu____62113 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___589_62133  ->
    match uu___589_62133 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _62139  -> FStar_TypeChecker_Common.TProb _62139)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _62145  -> FStar_TypeChecker_Common.CProb _62145)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___590_62151  ->
    match uu___590_62151 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___734_62157 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___734_62157.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___734_62157.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___734_62157.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___734_62157.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___734_62157.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___734_62157.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___734_62157.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___734_62157.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___734_62157.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___738_62165 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___738_62165.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___738_62165.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___738_62165.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___738_62165.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___738_62165.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___738_62165.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___738_62165.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___738_62165.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___738_62165.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___591_62178  ->
      match uu___591_62178 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___592_62185  ->
    match uu___592_62185 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___593_62198  ->
    match uu___593_62198 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___594_62213  ->
    match uu___594_62213 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___595_62228  ->
    match uu___595_62228 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___596_62242  ->
    match uu___596_62242 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___597_62256  ->
    match uu___597_62256 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___598_62268  ->
    match uu___598_62268 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____62284 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____62284) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____62314 =
          let uu____62316 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____62316  in
        if uu____62314
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____62353)::bs ->
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
          let uu____62400 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____62424 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____62424]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____62400
      | FStar_TypeChecker_Common.CProb p ->
          let uu____62452 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____62476 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____62476]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____62452
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____62523 =
          let uu____62525 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____62525  in
        if uu____62523
        then ()
        else
          (let uu____62530 =
             let uu____62533 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____62533
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____62530 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____62582 =
          let uu____62584 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____62584  in
        if uu____62582
        then ()
        else
          (let uu____62589 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____62589)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____62609 =
        let uu____62611 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____62611  in
      if uu____62609
      then ()
      else
        (let msgf m =
           let uu____62625 =
             let uu____62627 =
               let uu____62629 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____62629 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____62627  in
           Prims.op_Hat msg uu____62625  in
         (let uu____62634 = msgf "scope"  in
          let uu____62637 = p_scope prob  in
          def_scope_wf uu____62634 (p_loc prob) uu____62637);
         (let uu____62649 = msgf "guard"  in
          def_check_scoped uu____62649 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____62656 = msgf "lhs"  in
                def_check_scoped uu____62656 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____62659 = msgf "rhs"  in
                def_check_scoped uu____62659 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____62666 = msgf "lhs"  in
                def_check_scoped_comp uu____62666 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____62669 = msgf "rhs"  in
                def_check_scoped_comp uu____62669 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___831_62690 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___831_62690.wl_deferred);
          ctr = (uu___831_62690.ctr);
          defer_ok = (uu___831_62690.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___831_62690.umax_heuristic_ok);
          tcenv = (uu___831_62690.tcenv);
          wl_implicits = (uu___831_62690.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____62698 .
    FStar_TypeChecker_Env.env ->
      ('Auu____62698 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___835_62721 = empty_worklist env  in
      let uu____62722 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____62722;
        wl_deferred = (uu___835_62721.wl_deferred);
        ctr = (uu___835_62721.ctr);
        defer_ok = (uu___835_62721.defer_ok);
        smt_ok = (uu___835_62721.smt_ok);
        umax_heuristic_ok = (uu___835_62721.umax_heuristic_ok);
        tcenv = (uu___835_62721.tcenv);
        wl_implicits = (uu___835_62721.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___840_62745 = wl  in
        {
          attempting = (uu___840_62745.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___840_62745.ctr);
          defer_ok = (uu___840_62745.defer_ok);
          smt_ok = (uu___840_62745.smt_ok);
          umax_heuristic_ok = (uu___840_62745.umax_heuristic_ok);
          tcenv = (uu___840_62745.tcenv);
          wl_implicits = (uu___840_62745.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___845_62773 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___845_62773.wl_deferred);
         ctr = (uu___845_62773.ctr);
         defer_ok = (uu___845_62773.defer_ok);
         smt_ok = (uu___845_62773.smt_ok);
         umax_heuristic_ok = (uu___845_62773.umax_heuristic_ok);
         tcenv = (uu___845_62773.tcenv);
         wl_implicits = (uu___845_62773.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____62787 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____62787 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____62821 = FStar_Syntax_Util.type_u ()  in
            match uu____62821 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____62833 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____62833 with
                 | (uu____62851,tt,wl1) ->
                     let uu____62854 = FStar_Syntax_Util.mk_eq2 u tt t1 t2
                        in
                     (uu____62854, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___599_62860  ->
    match uu___599_62860 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _62866  -> FStar_TypeChecker_Common.TProb _62866) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _62872  -> FStar_TypeChecker_Common.CProb _62872) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____62880 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____62880 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____62900  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____62942 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____62942 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____62942 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____62942 FStar_TypeChecker_Common.problem *
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
                        let uu____63029 =
                          let uu____63038 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____63038]  in
                        FStar_List.append scope uu____63029
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____63081 =
                      let uu____63084 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____63084  in
                    FStar_List.append uu____63081
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____63103 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____63103 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____63129 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____63129;
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
                  (let uu____63203 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____63203 with
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
                  (let uu____63291 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____63291 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____63329 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____63329 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____63329 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____63329 FStar_TypeChecker_Common.problem *
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
                          let uu____63397 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____63397]  in
                        let uu____63416 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____63416
                     in
                  let uu____63419 =
                    let uu____63426 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___928_63437 = wl  in
                       {
                         attempting = (uu___928_63437.attempting);
                         wl_deferred = (uu___928_63437.wl_deferred);
                         ctr = (uu___928_63437.ctr);
                         defer_ok = (uu___928_63437.defer_ok);
                         smt_ok = (uu___928_63437.smt_ok);
                         umax_heuristic_ok =
                           (uu___928_63437.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___928_63437.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____63426
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____63419 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____63455 =
                              let uu____63460 =
                                let uu____63461 =
                                  let uu____63470 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____63470
                                   in
                                [uu____63461]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____63460
                               in
                            uu____63455 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____63498 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____63498;
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
                let uu____63546 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____63546;
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
  'Auu____63561 .
    worklist ->
      'Auu____63561 FStar_TypeChecker_Common.problem ->
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
              let uu____63594 =
                let uu____63597 =
                  let uu____63598 =
                    let uu____63605 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____63605)  in
                  FStar_Syntax_Syntax.NT uu____63598  in
                [uu____63597]  in
              FStar_Syntax_Subst.subst uu____63594 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____63629 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____63629
        then
          let uu____63637 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____63640 = prob_to_string env d  in
          let uu____63642 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____63637 uu____63640 uu____63642 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____63658 -> failwith "impossible"  in
           let uu____63661 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____63677 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____63679 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____63677, uu____63679)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____63686 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____63688 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____63686, uu____63688)
              in
           match uu____63661 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___600_63716  ->
            match uu___600_63716 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____63728 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____63732 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____63732 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___601_63763  ->
           match uu___601_63763 with
           | UNIV uu____63766 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____63773 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____63773
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
        (fun uu___602_63801  ->
           match uu___602_63801 with
           | UNIV (u',t) ->
               let uu____63806 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____63806
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____63813 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63825 =
        let uu____63826 =
          let uu____63827 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____63827
           in
        FStar_Syntax_Subst.compress uu____63826  in
      FStar_All.pipe_right uu____63825 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63839 =
        let uu____63840 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____63840  in
      FStar_All.pipe_right uu____63839 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____63848 = FStar_Syntax_Util.head_and_args t  in
    match uu____63848 with
    | (h,uu____63867) ->
        let uu____63892 =
          let uu____63893 = FStar_Syntax_Subst.compress h  in
          uu____63893.FStar_Syntax_Syntax.n  in
        (match uu____63892 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____63898 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63911 = should_strongly_reduce t  in
      if uu____63911
      then
        let uu____63914 =
          let uu____63915 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____63915  in
        FStar_All.pipe_right uu____63914 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____63925 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____63925) ->
        (FStar_Syntax_Syntax.term * 'Auu____63925)
  =
  fun env  ->
    fun t  ->
      let uu____63948 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____63948, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____64000  ->
              match uu____64000 with
              | (x,imp) ->
                  let uu____64019 =
                    let uu___1025_64020 = x  in
                    let uu____64021 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1025_64020.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1025_64020.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____64021
                    }  in
                  (uu____64019, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____64045 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____64045
        | FStar_Syntax_Syntax.U_max us ->
            let uu____64049 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____64049
        | uu____64052 -> u2  in
      let uu____64053 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____64053
  
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
                (let uu____64174 = norm_refinement env t12  in
                 match uu____64174 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____64189;
                     FStar_Syntax_Syntax.vars = uu____64190;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____64214 =
                       let uu____64216 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____64218 = FStar_Syntax_Print.tag_of_term tt
                          in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____64216 uu____64218
                        in
                     failwith uu____64214)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____64234 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____64234
          | FStar_Syntax_Syntax.Tm_uinst uu____64235 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____64272 =
                   let uu____64273 = FStar_Syntax_Subst.compress t1'  in
                   uu____64273.FStar_Syntax_Syntax.n  in
                 match uu____64272 with
                 | FStar_Syntax_Syntax.Tm_refine uu____64288 -> aux true t1'
                 | uu____64296 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____64311 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____64342 =
                   let uu____64343 = FStar_Syntax_Subst.compress t1'  in
                   uu____64343.FStar_Syntax_Syntax.n  in
                 match uu____64342 with
                 | FStar_Syntax_Syntax.Tm_refine uu____64358 -> aux true t1'
                 | uu____64366 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____64381 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____64428 =
                   let uu____64429 = FStar_Syntax_Subst.compress t1'  in
                   uu____64429.FStar_Syntax_Syntax.n  in
                 match uu____64428 with
                 | FStar_Syntax_Syntax.Tm_refine uu____64444 -> aux true t1'
                 | uu____64452 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____64467 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____64482 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____64497 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____64512 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____64527 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____64556 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____64589 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____64610 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____64637 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____64665 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____64702 ->
              let uu____64709 =
                let uu____64711 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64713 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64711 uu____64713
                 in
              failwith uu____64709
          | FStar_Syntax_Syntax.Tm_ascribed uu____64728 ->
              let uu____64755 =
                let uu____64757 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64759 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64757 uu____64759
                 in
              failwith uu____64755
          | FStar_Syntax_Syntax.Tm_delayed uu____64774 ->
              let uu____64797 =
                let uu____64799 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64801 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64799 uu____64801
                 in
              failwith uu____64797
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____64816 =
                let uu____64818 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64820 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64818 uu____64820
                 in
              failwith uu____64816
           in
        let uu____64835 = whnf env t1  in aux false uu____64835
  
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
      let uu____64896 = base_and_refinement env t  in
      FStar_All.pipe_right uu____64896 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____64937 = FStar_Syntax_Syntax.null_bv t  in
    (uu____64937, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____64964 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____64964 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____65024  ->
    match uu____65024 with
    | (t_base,refopt) ->
        let uu____65055 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____65055 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____65097 =
      let uu____65101 =
        let uu____65104 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____65131  ->
                  match uu____65131 with | (uu____65140,uu____65141,x) -> x))
           in
        FStar_List.append wl.attempting uu____65104  in
      FStar_List.map (wl_prob_to_string wl) uu____65101  in
    FStar_All.pipe_right uu____65097 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____65164 .
    ('Auu____65164 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____65176  ->
    match uu____65176 with
    | (uu____65183,c,args) ->
        let uu____65186 = print_ctx_uvar c  in
        let uu____65188 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____65186 uu____65188
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____65198 = FStar_Syntax_Util.head_and_args t  in
    match uu____65198 with
    | (head1,_args) ->
        let uu____65242 =
          let uu____65243 = FStar_Syntax_Subst.compress head1  in
          uu____65243.FStar_Syntax_Syntax.n  in
        (match uu____65242 with
         | FStar_Syntax_Syntax.Tm_uvar uu____65247 -> true
         | uu____65261 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____65269 = FStar_Syntax_Util.head_and_args t  in
    match uu____65269 with
    | (head1,_args) ->
        let uu____65312 =
          let uu____65313 = FStar_Syntax_Subst.compress head1  in
          uu____65313.FStar_Syntax_Syntax.n  in
        (match uu____65312 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____65317) -> u
         | uu____65334 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____65359 = FStar_Syntax_Util.head_and_args t  in
      match uu____65359 with
      | (head1,args) ->
          let uu____65406 =
            let uu____65407 = FStar_Syntax_Subst.compress head1  in
            uu____65407.FStar_Syntax_Syntax.n  in
          (match uu____65406 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____65415)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____65448 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___603_65473  ->
                         match uu___603_65473 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____65478 =
                               let uu____65479 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____65479.FStar_Syntax_Syntax.n  in
                             (match uu____65478 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____65484 -> false)
                         | uu____65486 -> true))
                  in
               (match uu____65448 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____65511 =
                        FStar_List.collect
                          (fun uu___604_65523  ->
                             match uu___604_65523 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____65527 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____65527]
                             | uu____65528 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____65511 FStar_List.rev  in
                    let uu____65551 =
                      let uu____65558 =
                        let uu____65567 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___605_65589  ->
                                  match uu___605_65589 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____65593 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____65593]
                                  | uu____65594 -> []))
                           in
                        FStar_All.pipe_right uu____65567 FStar_List.rev  in
                      let uu____65617 =
                        let uu____65620 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____65620  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____65558 uu____65617
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____65551 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____65656  ->
                                match uu____65656 with
                                | (x,i) ->
                                    let uu____65675 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____65675, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____65706  ->
                                match uu____65706 with
                                | (a,i) ->
                                    let uu____65725 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____65725, i)) args_sol
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
           | uu____65747 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____65769 =
          let uu____65792 =
            let uu____65793 = FStar_Syntax_Subst.compress k  in
            uu____65793.FStar_Syntax_Syntax.n  in
          match uu____65792 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____65875 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____65875)
              else
                (let uu____65910 = FStar_Syntax_Util.abs_formals t  in
                 match uu____65910 with
                 | (ys',t1,uu____65943) ->
                     let uu____65948 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____65948))
          | uu____65987 ->
              let uu____65988 =
                let uu____65993 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____65993)  in
              ((ys, t), uu____65988)
           in
        match uu____65769 with
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
                 let uu____66088 = FStar_Syntax_Util.rename_binders xs ys1
                    in
                 FStar_Syntax_Subst.subst_comp uu____66088 c  in
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
               (let uu____66166 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____66166
                then
                  let uu____66171 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____66173 = print_ctx_uvar uv  in
                  let uu____66175 = FStar_Syntax_Print.term_to_string phi1
                     in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____66171 uu____66173 uu____66175
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____66184 =
                   let uu____66186 = FStar_Util.string_of_int (p_pid prob)
                      in
                   Prims.op_Hat "solve_prob'.sol." uu____66186  in
                 let uu____66189 =
                   let uu____66192 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____66192
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____66184 uu____66189 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____66225 =
               let uu____66226 =
                 let uu____66228 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____66230 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____66228 uu____66230
                  in
               failwith uu____66226  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____66296  ->
                       match uu____66296 with
                       | (a,i) ->
                           let uu____66317 =
                             let uu____66318 = FStar_Syntax_Subst.compress a
                                in
                             uu____66318.FStar_Syntax_Syntax.n  in
                           (match uu____66317 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____66344 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____66354 =
                 let uu____66356 = is_flex g  in
                 Prims.op_Negation uu____66356  in
               if uu____66354
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____66365 = destruct_flex_t g wl  in
                  match uu____66365 with
                  | ((uu____66370,uv1,args),wl1) ->
                      ((let uu____66375 = args_as_binders args  in
                        assign_solution uu____66375 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___1277_66377 = wl1  in
              {
                attempting = (uu___1277_66377.attempting);
                wl_deferred = (uu___1277_66377.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___1277_66377.defer_ok);
                smt_ok = (uu___1277_66377.smt_ok);
                umax_heuristic_ok = (uu___1277_66377.umax_heuristic_ok);
                tcenv = (uu___1277_66377.tcenv);
                wl_implicits = (uu___1277_66377.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____66402 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____66402
         then
           let uu____66407 = FStar_Util.string_of_int pid  in
           let uu____66409 =
             let uu____66411 = FStar_List.map (uvi_to_string wl.tcenv) sol
                in
             FStar_All.pipe_right uu____66411 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____66407
             uu____66409
         else ());
        commit sol;
        (let uu___1285_66425 = wl  in
         {
           attempting = (uu___1285_66425.attempting);
           wl_deferred = (uu___1285_66425.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___1285_66425.defer_ok);
           smt_ok = (uu___1285_66425.smt_ok);
           umax_heuristic_ok = (uu___1285_66425.umax_heuristic_ok);
           tcenv = (uu___1285_66425.tcenv);
           wl_implicits = (uu___1285_66425.wl_implicits)
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
             | (uu____66491,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____66519 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____66519
              in
           (let uu____66525 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____66525
            then
              let uu____66530 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____66534 =
                let uu____66536 =
                  FStar_List.map (uvi_to_string wl.tcenv) uvis  in
                FStar_All.pipe_right uu____66536 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____66530
                uu____66534
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
        let uu____66571 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____66571 FStar_Util.set_elements  in
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
      let uu____66611 = occurs uk t  in
      match uu____66611 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____66650 =
                 let uu____66652 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____66654 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____66652 uu____66654
                  in
               FStar_Pervasives_Native.Some uu____66650)
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
            let uu____66774 = maximal_prefix bs_tail bs'_tail  in
            (match uu____66774 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____66825 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____66882  ->
             match uu____66882 with
             | (x,uu____66894) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____66912 = FStar_List.last bs  in
      match uu____66912 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____66936) ->
          let uu____66947 =
            FStar_Util.prefix_until
              (fun uu___606_66962  ->
                 match uu___606_66962 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____66965 -> false) g
             in
          (match uu____66947 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____66979,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____67016 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____67016 with
        | (pfx,uu____67026) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____67038 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____67038 with
             | (uu____67046,src',wl1) ->
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
                 | uu____67160 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____67161 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____67225  ->
                  fun uu____67226  ->
                    match (uu____67225, uu____67226) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____67329 =
                          let uu____67331 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____67331
                           in
                        if uu____67329
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____67365 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____67365
                           then
                             let uu____67382 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____67382)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____67161 with | (isect,uu____67432) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____67468 'Auu____67469 .
    (FStar_Syntax_Syntax.bv * 'Auu____67468) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____67469) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____67527  ->
              fun uu____67528  ->
                match (uu____67527, uu____67528) with
                | ((a,uu____67547),(b,uu____67549)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____67565 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____67565) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____67596  ->
           match uu____67596 with
           | (y,uu____67603) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____67613 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____67613) Prims.list ->
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
                   let uu____67775 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____67775
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____67808 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____67860 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____67905 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____67927 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___607_67935  ->
    match uu___607_67935 with
    | MisMatch (d1,d2) ->
        let uu____67947 =
          let uu____67949 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____67951 =
            let uu____67953 =
              let uu____67955 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____67955 ")"  in
            Prims.op_Hat ") (" uu____67953  in
          Prims.op_Hat uu____67949 uu____67951  in
        Prims.op_Hat "MisMatch (" uu____67947
    | HeadMatch u ->
        let uu____67962 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____67962
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___608_67971  ->
    match uu___608_67971 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____67988 -> HeadMatch false
  
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
          let uu____68010 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____68010 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____68021 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____68045 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____68055 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____68082 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____68082
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____68083 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____68084 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____68085 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____68098 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____68112 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____68136) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____68142,uu____68143) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____68185) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____68210;
             FStar_Syntax_Syntax.index = uu____68211;
             FStar_Syntax_Syntax.sort = t2;_},uu____68213)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____68221 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____68222 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____68223 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____68238 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____68245 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____68265 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____68265
  
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
           { FStar_Syntax_Syntax.blob = uu____68284;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____68285;
             FStar_Syntax_Syntax.ltyp = uu____68286;
             FStar_Syntax_Syntax.rng = uu____68287;_},uu____68288)
            ->
            let uu____68299 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____68299 t21
        | (uu____68300,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____68301;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____68302;
             FStar_Syntax_Syntax.ltyp = uu____68303;
             FStar_Syntax_Syntax.rng = uu____68304;_})
            ->
            let uu____68315 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____68315
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____68327 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____68327
            then FullMatch
            else
              (let uu____68332 =
                 let uu____68341 =
                   let uu____68344 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____68344  in
                 let uu____68345 =
                   let uu____68348 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____68348  in
                 (uu____68341, uu____68345)  in
               MisMatch uu____68332)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____68354),FStar_Syntax_Syntax.Tm_uinst (g,uu____68356)) ->
            let uu____68365 = head_matches env f g  in
            FStar_All.pipe_right uu____68365 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____68366) -> HeadMatch true
        | (uu____68368,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____68372 = FStar_Const.eq_const c d  in
            if uu____68372
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____68382),FStar_Syntax_Syntax.Tm_uvar (uv',uu____68384)) ->
            let uu____68417 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____68417
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____68427),FStar_Syntax_Syntax.Tm_refine (y,uu____68429)) ->
            let uu____68438 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____68438 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____68440),uu____68441) ->
            let uu____68446 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____68446 head_match
        | (uu____68447,FStar_Syntax_Syntax.Tm_refine (x,uu____68449)) ->
            let uu____68454 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____68454 head_match
        | (FStar_Syntax_Syntax.Tm_type
           uu____68455,FStar_Syntax_Syntax.Tm_type uu____68456) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____68458,FStar_Syntax_Syntax.Tm_arrow uu____68459) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____68490),FStar_Syntax_Syntax.Tm_app
           (head',uu____68492)) ->
            let uu____68541 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____68541 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____68543),uu____68544) ->
            let uu____68569 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____68569 head_match
        | (uu____68570,FStar_Syntax_Syntax.Tm_app (head1,uu____68572)) ->
            let uu____68597 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____68597 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____68598,FStar_Syntax_Syntax.Tm_let
           uu____68599) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____68627,FStar_Syntax_Syntax.Tm_match uu____68628) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____68674,FStar_Syntax_Syntax.Tm_abs
           uu____68675) -> HeadMatch true
        | uu____68713 ->
            let uu____68718 =
              let uu____68727 = delta_depth_of_term env t11  in
              let uu____68730 = delta_depth_of_term env t21  in
              (uu____68727, uu____68730)  in
            MisMatch uu____68718
  
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
            (let uu____68796 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____68796
             then
               let uu____68801 = FStar_Syntax_Print.term_to_string t  in
               let uu____68803 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____68801 uu____68803
             else ());
            (let uu____68808 =
               let uu____68809 = FStar_Syntax_Util.un_uinst head1  in
               uu____68809.FStar_Syntax_Syntax.n  in
             match uu____68808 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____68815 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____68815 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____68829 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____68829
                        then
                          let uu____68834 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____68834
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____68839 ->
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
                      let uu____68856 =
                        let uu____68858 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____68858 = FStar_Syntax_Util.Equal  in
                      if uu____68856
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____68865 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____68865
                          then
                            let uu____68870 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____68872 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n"
                              uu____68870 uu____68872
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____68877 -> FStar_Pervasives_Native.None)
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
            (let uu____69029 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____69029
             then
               let uu____69034 = FStar_Syntax_Print.term_to_string t11  in
               let uu____69036 = FStar_Syntax_Print.term_to_string t21  in
               let uu____69038 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____69034
                 uu____69036 uu____69038
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____69066 =
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
               match uu____69066 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____69114 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____69114 with
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
                  uu____69152),uu____69153)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____69174 =
                      let uu____69183 = maybe_inline t11  in
                      let uu____69186 = maybe_inline t21  in
                      (uu____69183, uu____69186)  in
                    match uu____69174 with
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
                 (uu____69229,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____69230))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____69251 =
                      let uu____69260 = maybe_inline t11  in
                      let uu____69263 = maybe_inline t21  in
                      (uu____69260, uu____69263)  in
                    match uu____69251 with
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
             | MisMatch uu____69318 -> fail1 n_delta r t11 t21
             | uu____69327 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____69342 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____69342
           then
             let uu____69347 = FStar_Syntax_Print.term_to_string t1  in
             let uu____69349 = FStar_Syntax_Print.term_to_string t2  in
             let uu____69351 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____69359 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____69376 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____69376
                    (fun uu____69411  ->
                       match uu____69411 with
                       | (t11,t21) ->
                           let uu____69419 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____69421 =
                             let uu____69423 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____69423  in
                           Prims.op_Hat uu____69419 uu____69421))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____69347 uu____69349 uu____69351 uu____69359
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____69440 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____69440 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___609_69455  ->
    match uu___609_69455 with
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
      let uu___1789_69504 = p  in
      let uu____69507 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____69508 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1789_69504.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____69507;
        FStar_TypeChecker_Common.relation =
          (uu___1789_69504.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____69508;
        FStar_TypeChecker_Common.element =
          (uu___1789_69504.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1789_69504.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1789_69504.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1789_69504.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1789_69504.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1789_69504.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____69523 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____69523
            (fun _69528  -> FStar_TypeChecker_Common.TProb _69528)
      | FStar_TypeChecker_Common.CProb uu____69529 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____69552 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____69552 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____69560 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____69560 with
           | (lh,lhs_args) ->
               let uu____69607 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____69607 with
                | (rh,rhs_args) ->
                    let uu____69654 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____69667,FStar_Syntax_Syntax.Tm_uvar uu____69668)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____69757 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____69784,uu____69785)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____69800,FStar_Syntax_Syntax.Tm_uvar uu____69801)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____69816,FStar_Syntax_Syntax.Tm_arrow
                         uu____69817) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69847 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69847.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69847.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69847.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69847.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69847.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69847.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69847.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69847.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69847.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____69850,FStar_Syntax_Syntax.Tm_type uu____69851)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69867 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69867.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69867.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69867.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69867.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69867.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69867.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69867.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69867.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69867.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____69870,FStar_Syntax_Syntax.Tm_uvar uu____69871)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69887 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69887.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69887.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69887.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69887.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69887.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69887.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69887.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69887.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69887.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____69890,FStar_Syntax_Syntax.Tm_uvar uu____69891)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____69906,uu____69907)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____69922,FStar_Syntax_Syntax.Tm_uvar uu____69923)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____69938,uu____69939) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____69654 with
                     | (rank,tp1) ->
                         let uu____69952 =
                           FStar_All.pipe_right
                             (let uu___1860_69956 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1860_69956.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1860_69956.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1860_69956.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1860_69956.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1860_69956.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1860_69956.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1860_69956.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1860_69956.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1860_69956.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _69959  ->
                                FStar_TypeChecker_Common.TProb _69959)
                            in
                         (rank, uu____69952))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____69963 =
            FStar_All.pipe_right
              (let uu___1864_69967 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1864_69967.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1864_69967.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1864_69967.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1864_69967.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1864_69967.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1864_69967.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1864_69967.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1864_69967.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1864_69967.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _69970  -> FStar_TypeChecker_Common.CProb _69970)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____69963)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____70030 probs =
      match uu____70030 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____70111 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____70132 = rank wl.tcenv hd1  in
               (match uu____70132 with
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
                      (let uu____70193 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____70198 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____70198)
                          in
                       if uu____70193
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
          let uu____70271 = FStar_Syntax_Util.head_and_args t  in
          match uu____70271 with
          | (hd1,uu____70290) ->
              let uu____70315 =
                let uu____70316 = FStar_Syntax_Subst.compress hd1  in
                uu____70316.FStar_Syntax_Syntax.n  in
              (match uu____70315 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____70321) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____70356  ->
                           match uu____70356 with
                           | (y,uu____70365) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____70388  ->
                                       match uu____70388 with
                                       | (x,uu____70397) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____70402 -> false)
           in
        let uu____70404 = rank tcenv p  in
        match uu____70404 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____70413 -> true
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
    match projectee with | UDeferred _0 -> true | uu____70450 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____70470 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____70491 -> false
  
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
                        let uu____70554 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____70554 with
                        | (k,uu____70562) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____70575 -> false)))
            | uu____70577 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____70629 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____70637 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____70637 = (Prims.parse_int "0")))
                           in
                        if uu____70629 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____70658 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____70666 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____70666 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____70658)
               in
            let uu____70670 = filter1 u12  in
            let uu____70673 = filter1 u22  in (uu____70670, uu____70673)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____70708 = filter_out_common_univs us1 us2  in
                   (match uu____70708 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____70768 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____70768 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____70771 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____70782 =
                             let uu____70784 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____70786 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____70784 uu____70786
                              in
                           UFailed uu____70782))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____70812 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____70812 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____70838 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____70838 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____70841 ->
                   let uu____70846 =
                     let uu____70848 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____70850 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)"
                       uu____70848 uu____70850 msg
                      in
                   UFailed uu____70846)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____70853,uu____70854) ->
              let uu____70856 =
                let uu____70858 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70860 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70858 uu____70860
                 in
              failwith uu____70856
          | (FStar_Syntax_Syntax.U_unknown ,uu____70863) ->
              let uu____70864 =
                let uu____70866 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70868 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70866 uu____70868
                 in
              failwith uu____70864
          | (uu____70871,FStar_Syntax_Syntax.U_bvar uu____70872) ->
              let uu____70874 =
                let uu____70876 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70878 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70876 uu____70878
                 in
              failwith uu____70874
          | (uu____70881,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____70882 =
                let uu____70884 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70886 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70884 uu____70886
                 in
              failwith uu____70882
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____70916 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____70916
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____70933 = occurs_univ v1 u3  in
              if uu____70933
              then
                let uu____70936 =
                  let uu____70938 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____70940 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____70938 uu____70940
                   in
                try_umax_components u11 u21 uu____70936
              else
                (let uu____70945 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____70945)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____70957 = occurs_univ v1 u3  in
              if uu____70957
              then
                let uu____70960 =
                  let uu____70962 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____70964 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____70962 uu____70964
                   in
                try_umax_components u11 u21 uu____70960
              else
                (let uu____70969 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____70969)
          | (FStar_Syntax_Syntax.U_max uu____70970,uu____70971) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____70979 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____70979
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____70985,FStar_Syntax_Syntax.U_max uu____70986) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____70994 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____70994
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____71000,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____71002,FStar_Syntax_Syntax.U_name uu____71003) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____71005) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____71007) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____71009,FStar_Syntax_Syntax.U_succ uu____71010) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____71012,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____71119 = bc1  in
      match uu____71119 with
      | (bs1,mk_cod1) ->
          let uu____71163 = bc2  in
          (match uu____71163 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____71274 = aux xs ys  in
                     (match uu____71274 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____71357 =
                       let uu____71364 = mk_cod1 xs  in ([], uu____71364)  in
                     let uu____71367 =
                       let uu____71374 = mk_cod2 ys  in ([], uu____71374)  in
                     (uu____71357, uu____71367)
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
                  let uu____71443 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____71443 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____71446 =
                    let uu____71447 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____71447 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____71446
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____71452 = has_type_guard t1 t2  in (uu____71452, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____71453 = has_type_guard t2 t1  in (uu____71453, wl)
  
let is_flex_pat :
  'Auu____71463 'Auu____71464 'Auu____71465 .
    ('Auu____71463 * 'Auu____71464 * 'Auu____71465 Prims.list) -> Prims.bool
  =
  fun uu___610_71479  ->
    match uu___610_71479 with
    | (uu____71488,uu____71489,[]) -> true
    | uu____71493 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____71526 = f  in
      match uu____71526 with
      | (uu____71533,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____71534;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____71535;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____71538;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____71539;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____71540;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____71541;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____71611  ->
                 match uu____71611 with
                 | (y,uu____71620) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____71774 =
                  let uu____71789 =
                    let uu____71792 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____71792  in
                  ((FStar_List.rev pat_binders), uu____71789)  in
                FStar_Pervasives_Native.Some uu____71774
            | (uu____71825,[]) ->
                let uu____71856 =
                  let uu____71871 =
                    let uu____71874 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____71874  in
                  ((FStar_List.rev pat_binders), uu____71871)  in
                FStar_Pervasives_Native.Some uu____71856
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____71965 =
                  let uu____71966 = FStar_Syntax_Subst.compress a  in
                  uu____71966.FStar_Syntax_Syntax.n  in
                (match uu____71965 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____71986 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____71986
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___2188_72016 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___2188_72016.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___2188_72016.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____72020 =
                            let uu____72021 =
                              let uu____72028 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____72028)  in
                            FStar_Syntax_Syntax.NT uu____72021  in
                          [uu____72020]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___2194_72044 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2194_72044.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2194_72044.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____72045 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____72085 =
                  let uu____72100 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____72100  in
                (match uu____72085 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____72175 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____72208 ->
               let uu____72209 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____72209 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____72531 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____72531
       then
         let uu____72536 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____72536
       else ());
      (let uu____72541 = next_prob probs  in
       match uu____72541 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___2219_72568 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___2219_72568.wl_deferred);
               ctr = (uu___2219_72568.ctr);
               defer_ok = (uu___2219_72568.defer_ok);
               smt_ok = (uu___2219_72568.smt_ok);
               umax_heuristic_ok = (uu___2219_72568.umax_heuristic_ok);
               tcenv = (uu___2219_72568.tcenv);
               wl_implicits = (uu___2219_72568.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____72577 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____72577
                 then
                   let uu____72580 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____72580
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
                           (let uu___2231_72592 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___2231_72592.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___2231_72592.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___2231_72592.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___2231_72592.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___2231_72592.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___2231_72592.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___2231_72592.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___2231_72592.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___2231_72592.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____72618 ->
                let uu____72629 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____72700  ->
                          match uu____72700 with
                          | (c,uu____72711,uu____72712) -> c < probs.ctr))
                   in
                (match uu____72629 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____72767 =
                            let uu____72772 =
                              FStar_List.map
                                (fun uu____72790  ->
                                   match uu____72790 with
                                   | (uu____72804,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____72772, (probs.wl_implicits))  in
                          Success uu____72767
                      | uu____72812 ->
                          let uu____72823 =
                            let uu___2249_72824 = probs  in
                            let uu____72825 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____72848  ->
                                      match uu____72848 with
                                      | (uu____72857,uu____72858,y) -> y))
                               in
                            {
                              attempting = uu____72825;
                              wl_deferred = rest;
                              ctr = (uu___2249_72824.ctr);
                              defer_ok = (uu___2249_72824.defer_ok);
                              smt_ok = (uu___2249_72824.smt_ok);
                              umax_heuristic_ok =
                                (uu___2249_72824.umax_heuristic_ok);
                              tcenv = (uu___2249_72824.tcenv);
                              wl_implicits = (uu___2249_72824.wl_implicits)
                            }  in
                          solve env uu____72823))))

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
            let uu____72869 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____72869 with
            | USolved wl1 ->
                let uu____72871 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____72871
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
                  let uu____72925 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____72925 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____72928 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____72941;
                  FStar_Syntax_Syntax.vars = uu____72942;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____72945;
                  FStar_Syntax_Syntax.vars = uu____72946;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____72959,uu____72960) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____72968,FStar_Syntax_Syntax.Tm_uinst uu____72969) ->
                failwith "Impossible: expect head symbols to match"
            | uu____72977 -> USolved wl

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
            ((let uu____72989 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____72989
              then
                let uu____72994 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____72994 msg
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
               let uu____73086 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____73086 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____73141 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____73141
                then
                  let uu____73146 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____73148 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____73146 uu____73148
                else ());
               (let uu____73153 = head_matches_delta env1 wl2 t1 t2  in
                match uu____73153 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____73199 = eq_prob t1 t2 wl2  in
                         (match uu____73199 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____73220 ->
                         let uu____73229 = eq_prob t1 t2 wl2  in
                         (match uu____73229 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____73279 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____73294 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____73295 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____73294, uu____73295)
                           | FStar_Pervasives_Native.None  ->
                               let uu____73300 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____73301 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____73300, uu____73301)
                            in
                         (match uu____73279 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____73332 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____73332 with
                                | (t1_hd,t1_args) ->
                                    let uu____73377 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____73377 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____73443 =
                                              let uu____73450 =
                                                let uu____73461 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____73461 :: t1_args  in
                                              let uu____73478 =
                                                let uu____73487 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____73487 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____73536  ->
                                                   fun uu____73537  ->
                                                     fun uu____73538  ->
                                                       match (uu____73536,
                                                               uu____73537,
                                                               uu____73538)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____73588),
                                                          (a2,uu____73590))
                                                           ->
                                                           let uu____73627 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____73627
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____73450
                                                uu____73478
                                               in
                                            match uu____73443 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___2403_73653 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___2403_73653.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___2403_73653.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___2403_73653.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____73665 =
                                                  solve env1 wl'  in
                                                (match uu____73665 with
                                                 | Success (uu____73668,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___2412_73672
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___2412_73672.attempting);
                                                            wl_deferred =
                                                              (uu___2412_73672.wl_deferred);
                                                            ctr =
                                                              (uu___2412_73672.ctr);
                                                            defer_ok =
                                                              (uu___2412_73672.defer_ok);
                                                            smt_ok =
                                                              (uu___2412_73672.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___2412_73672.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___2412_73672.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____73673 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____73706 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____73706 with
                                | (t1_base,p1_opt) ->
                                    let uu____73742 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____73742 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____73841 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____73841
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
                                               let uu____73894 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____73894
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
                                               let uu____73926 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____73926
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
                                               let uu____73958 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____73958
                                           | uu____73961 -> t_base  in
                                         let uu____73978 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____73978 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____73992 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____73992, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____73999 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____73999 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____74035 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____74035 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____74071 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____74071
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
                              let uu____74095 = combine t11 t21 wl2  in
                              (match uu____74095 with
                               | (t12,ps,wl3) ->
                                   ((let uu____74128 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____74128
                                     then
                                       let uu____74133 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____74133
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____74175 ts1 =
               match uu____74175 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____74238 = pairwise out t wl2  in
                        (match uu____74238 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____74274 =
               let uu____74285 = FStar_List.hd ts  in (uu____74285, [], wl1)
                in
             let uu____74294 = FStar_List.tl ts  in
             aux uu____74274 uu____74294  in
           let uu____74301 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____74301 with
           | (this_flex,this_rigid) ->
               let uu____74327 =
                 let uu____74328 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____74328.FStar_Syntax_Syntax.n  in
               (match uu____74327 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____74353 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____74353
                    then
                      let uu____74356 = destruct_flex_t this_flex wl  in
                      (match uu____74356 with
                       | (flex,wl1) ->
                           let uu____74363 = quasi_pattern env flex  in
                           (match uu____74363 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____74382 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____74382
                                  then
                                    let uu____74387 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____74387
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____74394 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2514_74397 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2514_74397.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2514_74397.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2514_74397.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2514_74397.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2514_74397.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2514_74397.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2514_74397.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2514_74397.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2514_74397.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____74394)
                | uu____74398 ->
                    ((let uu____74400 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____74400
                      then
                        let uu____74405 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____74405
                      else ());
                     (let uu____74410 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____74410 with
                      | (u,_args) ->
                          let uu____74453 =
                            let uu____74454 = FStar_Syntax_Subst.compress u
                               in
                            uu____74454.FStar_Syntax_Syntax.n  in
                          (match uu____74453 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____74482 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____74482 with
                                 | (u',uu____74501) ->
                                     let uu____74526 =
                                       let uu____74527 = whnf env u'  in
                                       uu____74527.FStar_Syntax_Syntax.n  in
                                     (match uu____74526 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____74549 -> false)
                                  in
                               let uu____74551 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___611_74574  ->
                                         match uu___611_74574 with
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
                                              | uu____74588 -> false)
                                         | uu____74592 -> false))
                                  in
                               (match uu____74551 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____74607 = whnf env this_rigid
                                         in
                                      let uu____74608 =
                                        FStar_List.collect
                                          (fun uu___612_74614  ->
                                             match uu___612_74614 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____74620 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____74620]
                                             | uu____74624 -> [])
                                          bounds_probs
                                         in
                                      uu____74607 :: uu____74608  in
                                    let uu____74625 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____74625 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____74658 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____74673 =
                                               let uu____74674 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____74674.FStar_Syntax_Syntax.n
                                                in
                                             match uu____74673 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____74686 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____74686)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____74697 -> bound  in
                                           let uu____74698 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____74698)  in
                                         (match uu____74658 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____74733 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____74733
                                                then
                                                  let wl'1 =
                                                    let uu___2574_74739 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2574_74739.wl_deferred);
                                                      ctr =
                                                        (uu___2574_74739.ctr);
                                                      defer_ok =
                                                        (uu___2574_74739.defer_ok);
                                                      smt_ok =
                                                        (uu___2574_74739.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2574_74739.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2574_74739.tcenv);
                                                      wl_implicits =
                                                        (uu___2574_74739.wl_implicits)
                                                    }  in
                                                  let uu____74740 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____74740
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____74746 =
                                                  solve_t env eq_prob
                                                    (let uu___2579_74748 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2579_74748.wl_deferred);
                                                       ctr =
                                                         (uu___2579_74748.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2579_74748.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2579_74748.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2579_74748.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____74746 with
                                                | Success (uu____74750,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2585_74753 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2585_74753.wl_deferred);
                                                        ctr =
                                                          (uu___2585_74753.ctr);
                                                        defer_ok =
                                                          (uu___2585_74753.defer_ok);
                                                        smt_ok =
                                                          (uu___2585_74753.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2585_74753.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2585_74753.tcenv);
                                                        wl_implicits =
                                                          (uu___2585_74753.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2588_74755 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2588_74755.attempting);
                                                        wl_deferred =
                                                          (uu___2588_74755.wl_deferred);
                                                        ctr =
                                                          (uu___2588_74755.ctr);
                                                        defer_ok =
                                                          (uu___2588_74755.defer_ok);
                                                        smt_ok =
                                                          (uu___2588_74755.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2588_74755.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2588_74755.tcenv);
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
                                                    let uu____74771 =
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
                                                    ((let uu____74785 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____74785
                                                      then
                                                        let uu____74790 =
                                                          let uu____74792 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____74792
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____74790
                                                      else ());
                                                     (let uu____74805 =
                                                        let uu____74820 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____74820)
                                                         in
                                                      match uu____74805 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____74842))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____74868 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____74868
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
                                                                  let uu____74888
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____74888))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____74913 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____74913
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
                                                                    let uu____74933
                                                                    =
                                                                    let uu____74938
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____74938
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____74933
                                                                    [] wl2
                                                                     in
                                                                  let uu____74944
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____74944))))
                                                      | uu____74945 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____74961 when flip ->
                               let uu____74962 =
                                 let uu____74964 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____74966 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____74964 uu____74966
                                  in
                               failwith uu____74962
                           | uu____74969 ->
                               let uu____74970 =
                                 let uu____74972 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____74974 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____74972 uu____74974
                                  in
                               failwith uu____74970)))))

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
                      (fun uu____75010  ->
                         match uu____75010 with
                         | (x,i) ->
                             let uu____75029 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____75029, i)) bs_lhs
                     in
                  let uu____75032 = lhs  in
                  match uu____75032 with
                  | (uu____75033,u_lhs,uu____75035) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____75132 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____75142 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____75142, univ)
                             in
                          match uu____75132 with
                          | (k,univ) ->
                              let uu____75149 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____75149 with
                               | (uu____75166,u,wl3) ->
                                   let uu____75169 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____75169, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____75195 =
                              let uu____75208 =
                                let uu____75219 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____75219 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____75270  ->
                                   fun uu____75271  ->
                                     match (uu____75270, uu____75271) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____75372 =
                                           let uu____75379 =
                                             let uu____75382 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____75382
                                              in
                                           copy_uvar u_lhs [] uu____75379 wl2
                                            in
                                         (match uu____75372 with
                                          | (uu____75411,t_a,wl3) ->
                                              let uu____75414 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____75414 with
                                               | (uu____75433,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____75208
                                ([], wl1)
                               in
                            (match uu____75195 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2698_75489 = ct  in
                                   let uu____75490 =
                                     let uu____75493 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____75493
                                      in
                                   let uu____75508 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2698_75489.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2698_75489.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____75490;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____75508;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2698_75489.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2701_75526 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2701_75526.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2701_75526.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____75529 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____75529 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____75591 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____75591 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____75602 =
                                          let uu____75607 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____75607)  in
                                        TERM uu____75602  in
                                      let uu____75608 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____75608 with
                                       | (sub_prob,wl3) ->
                                           let uu____75622 =
                                             let uu____75623 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____75623
                                              in
                                           solve env uu____75622))
                             | (x,imp)::formals2 ->
                                 let uu____75645 =
                                   let uu____75652 =
                                     let uu____75655 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____75655
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____75652 wl1
                                    in
                                 (match uu____75645 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____75676 =
                                          let uu____75679 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____75679
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____75676 u_x
                                         in
                                      let uu____75680 =
                                        let uu____75683 =
                                          let uu____75686 =
                                            let uu____75687 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____75687, imp)  in
                                          [uu____75686]  in
                                        FStar_List.append bs_terms
                                          uu____75683
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____75680 formals2 wl2)
                              in
                           let uu____75714 = occurs_check u_lhs arrow1  in
                           (match uu____75714 with
                            | (uu____75727,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____75743 =
                                    let uu____75745 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____75745
                                     in
                                  giveup_or_defer env orig wl uu____75743
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
              (let uu____75778 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____75778
               then
                 let uu____75783 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____75786 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____75783 (rel_to_string (p_rel orig)) uu____75786
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____75913 = rhs wl1 scope env1 subst1  in
                     (match uu____75913 with
                      | (rhs_prob,wl2) ->
                          ((let uu____75934 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____75934
                            then
                              let uu____75939 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____75939
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____76017 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____76017 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2770_76019 = hd1  in
                       let uu____76020 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2770_76019.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2770_76019.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____76020
                       }  in
                     let hd21 =
                       let uu___2773_76024 = hd2  in
                       let uu____76025 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2773_76024.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2773_76024.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____76025
                       }  in
                     let uu____76028 =
                       let uu____76033 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____76033
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____76028 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____76054 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____76054
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____76061 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____76061 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____76128 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____76128
                                  in
                               ((let uu____76146 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____76146
                                 then
                                   let uu____76151 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____76153 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____76151
                                     uu____76153
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____76186 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____76222 = aux wl [] env [] bs1 bs2  in
               match uu____76222 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____76277 = attempt sub_probs wl2  in
                   solve env uu____76277)

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
            let uu___2808_76298 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2808_76298.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2808_76298.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____76311 = try_solve env wl'  in
          match uu____76311 with
          | Success (uu____76312,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2817_76316 = wl  in
                  {
                    attempting = (uu___2817_76316.attempting);
                    wl_deferred = (uu___2817_76316.wl_deferred);
                    ctr = (uu___2817_76316.ctr);
                    defer_ok = (uu___2817_76316.defer_ok);
                    smt_ok = (uu___2817_76316.smt_ok);
                    umax_heuristic_ok = (uu___2817_76316.umax_heuristic_ok);
                    tcenv = (uu___2817_76316.tcenv);
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
        (let uu____76328 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____76328 wl)

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
              let uu____76342 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____76342 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____76376 = lhs1  in
              match uu____76376 with
              | (uu____76379,ctx_u,uu____76381) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____76389 ->
                        let uu____76390 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____76390 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____76439 = quasi_pattern env1 lhs1  in
              match uu____76439 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____76473) ->
                  let uu____76478 = lhs1  in
                  (match uu____76478 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____76493 = occurs_check ctx_u rhs1  in
                       (match uu____76493 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____76544 =
                                let uu____76552 =
                                  let uu____76554 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____76554
                                   in
                                FStar_Util.Inl uu____76552  in
                              (uu____76544, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____76582 =
                                 let uu____76584 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____76584  in
                               if uu____76582
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____76611 =
                                    let uu____76619 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____76619  in
                                  let uu____76625 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____76611, uu____76625)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____76669 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____76669 with
              | (rhs_hd,args) ->
                  let uu____76712 = FStar_Util.prefix args  in
                  (match uu____76712 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____76784 = lhs1  in
                       (match uu____76784 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____76788 =
                              let uu____76799 =
                                let uu____76806 =
                                  let uu____76809 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____76809
                                   in
                                copy_uvar u_lhs [] uu____76806 wl1  in
                              match uu____76799 with
                              | (uu____76836,t_last_arg,wl2) ->
                                  let uu____76839 =
                                    let uu____76846 =
                                      let uu____76847 =
                                        let uu____76856 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____76856]  in
                                      FStar_List.append bs_lhs uu____76847
                                       in
                                    copy_uvar u_lhs uu____76846 t_res_lhs wl2
                                     in
                                  (match uu____76839 with
                                   | (uu____76891,lhs',wl3) ->
                                       let uu____76894 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____76894 with
                                        | (uu____76911,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____76788 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____76932 =
                                     let uu____76933 =
                                       let uu____76938 =
                                         let uu____76939 =
                                           let uu____76942 =
                                             let uu____76947 =
                                               let uu____76948 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____76948]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____76947
                                              in
                                           uu____76942
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____76939
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____76938)  in
                                     TERM uu____76933  in
                                   [uu____76932]  in
                                 let uu____76973 =
                                   let uu____76980 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____76980 with
                                   | (p1,wl3) ->
                                       let uu____77000 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____77000 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____76973 with
                                  | (sub_probs,wl3) ->
                                      let uu____77032 =
                                        let uu____77033 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____77033  in
                                      solve env1 uu____77032))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____77067 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____77067 with
                | (uu____77085,args) ->
                    (match args with | [] -> false | uu____77121 -> true)
                 in
              let is_arrow rhs2 =
                let uu____77140 =
                  let uu____77141 = FStar_Syntax_Subst.compress rhs2  in
                  uu____77141.FStar_Syntax_Syntax.n  in
                match uu____77140 with
                | FStar_Syntax_Syntax.Tm_arrow uu____77145 -> true
                | uu____77161 -> false  in
              let uu____77163 = quasi_pattern env1 lhs1  in
              match uu____77163 with
              | FStar_Pervasives_Native.None  ->
                  let uu____77174 =
                    let uu____77176 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____77176
                     in
                  giveup_or_defer env1 orig1 wl1 uu____77174
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____77185 = is_app rhs1  in
                  if uu____77185
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____77190 = is_arrow rhs1  in
                     if uu____77190
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____77195 =
                          let uu____77197 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____77197
                           in
                        giveup_or_defer env1 orig1 wl1 uu____77195))
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
                let uu____77208 = lhs  in
                (match uu____77208 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____77212 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____77212 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____77230 =
                              let uu____77234 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____77234
                               in
                            FStar_All.pipe_right uu____77230
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____77255 = occurs_check ctx_uv rhs1  in
                          (match uu____77255 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____77284 =
                                   let uu____77286 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____77286
                                    in
                                 giveup_or_defer env orig wl uu____77284
                               else
                                 (let uu____77292 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____77292
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____77299 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____77299
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____77303 =
                                         let uu____77305 =
                                           names_to_string1 fvs2  in
                                         let uu____77307 =
                                           names_to_string1 fvs1  in
                                         let uu____77309 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____77305 uu____77307
                                           uu____77309
                                          in
                                       giveup_or_defer env orig wl
                                         uu____77303)
                                    else first_order orig env wl lhs rhs1))
                      | uu____77321 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____77328 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____77328 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____77354 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____77354
                             | (FStar_Util.Inl msg,uu____77356) ->
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
                  (let uu____77401 =
                     let uu____77418 = quasi_pattern env lhs  in
                     let uu____77425 = quasi_pattern env rhs  in
                     (uu____77418, uu____77425)  in
                   match uu____77401 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____77468 = lhs  in
                       (match uu____77468 with
                        | ({ FStar_Syntax_Syntax.n = uu____77469;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____77471;_},u_lhs,uu____77473)
                            ->
                            let uu____77476 = rhs  in
                            (match uu____77476 with
                             | (uu____77477,u_rhs,uu____77479) ->
                                 let uu____77480 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____77480
                                 then
                                   let uu____77487 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____77487
                                 else
                                   (let uu____77490 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____77490 with
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
                                        let uu____77522 =
                                          let uu____77529 =
                                            let uu____77532 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____77532
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____77529
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____77522 with
                                         | (uu____77544,w,wl1) ->
                                             let w_app =
                                               let uu____77550 =
                                                 let uu____77555 =
                                                   FStar_List.map
                                                     (fun uu____77566  ->
                                                        match uu____77566
                                                        with
                                                        | (z,uu____77574) ->
                                                            let uu____77579 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____77579) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____77555
                                                  in
                                               uu____77550
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____77581 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____77581
                                               then
                                                 let uu____77586 =
                                                   let uu____77590 =
                                                     flex_t_to_string lhs  in
                                                   let uu____77592 =
                                                     let uu____77596 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____77598 =
                                                       let uu____77602 =
                                                         term_to_string w  in
                                                       let uu____77604 =
                                                         let uu____77608 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____77617 =
                                                           let uu____77621 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____77630 =
                                                             let uu____77634
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____77634]
                                                              in
                                                           uu____77621 ::
                                                             uu____77630
                                                            in
                                                         uu____77608 ::
                                                           uu____77617
                                                          in
                                                       uu____77602 ::
                                                         uu____77604
                                                        in
                                                     uu____77596 ::
                                                       uu____77598
                                                      in
                                                   uu____77590 :: uu____77592
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____77586
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____77651 =
                                                     let uu____77656 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____77656)  in
                                                   TERM uu____77651  in
                                                 let uu____77657 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____77657
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____77665 =
                                                        let uu____77670 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____77670)
                                                         in
                                                      TERM uu____77665  in
                                                    [s1; s2])
                                                  in
                                               let uu____77671 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____77671))))))
                   | uu____77672 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____77743 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____77743
            then
              let uu____77748 = FStar_Syntax_Print.term_to_string t1  in
              let uu____77750 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____77752 = FStar_Syntax_Print.term_to_string t2  in
              let uu____77754 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____77748 uu____77750 uu____77752 uu____77754
            else ());
           (let uu____77765 = FStar_Syntax_Util.head_and_args t1  in
            match uu____77765 with
            | (head1,args1) ->
                let uu____77808 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____77808 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____77878 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____77878 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____77904 =
                         let uu____77906 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____77908 = args_to_string args1  in
                         let uu____77912 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____77914 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____77906 uu____77908 uu____77912 uu____77914
                          in
                       giveup env1 uu____77904 orig
                     else
                       (let uu____77921 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____77926 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____77926 = FStar_Syntax_Util.Equal)
                           in
                        if uu____77921
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___3066_77930 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___3066_77930.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___3066_77930.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___3066_77930.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___3066_77930.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___3066_77930.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___3066_77930.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___3066_77930.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___3066_77930.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____77940 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____77940
                                    else solve env1 wl2))
                        else
                          (let uu____77945 = base_and_refinement env1 t1  in
                           match uu____77945 with
                           | (base1,refinement1) ->
                               let uu____77970 = base_and_refinement env1 t2
                                  in
                               (match uu____77970 with
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
                                           let uu____78135 =
                                             FStar_List.fold_right
                                               (fun uu____78175  ->
                                                  fun uu____78176  ->
                                                    match (uu____78175,
                                                            uu____78176)
                                                    with
                                                    | (((a1,uu____78228),
                                                        (a2,uu____78230)),
                                                       (probs,wl3)) ->
                                                        let uu____78279 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____78279
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____78135 with
                                           | (subprobs,wl3) ->
                                               ((let uu____78322 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____78322
                                                 then
                                                   let uu____78327 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____78327
                                                 else ());
                                                (let uu____78333 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____78333
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
                                                    (let uu____78360 =
                                                       mk_sub_probs wl3  in
                                                     match uu____78360 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____78376 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____78376
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____78384 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____78384))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____78408 =
                                                    mk_sub_probs wl3  in
                                                  match uu____78408 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____78422 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____78422)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____78448 =
                                           match uu____78448 with
                                           | (prob,reason) ->
                                               ((let uu____78459 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____78459
                                                 then
                                                   let uu____78464 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____78466 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____78464 uu____78466
                                                     reason
                                                 else ());
                                                (let uu____78471 =
                                                   let uu____78480 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____78483 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____78480, uu____78483)
                                                    in
                                                 match uu____78471 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____78496 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____78496 with
                                                      | (head1',uu____78514)
                                                          ->
                                                          let uu____78539 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____78539
                                                           with
                                                           | (head2',uu____78557)
                                                               ->
                                                               let uu____78582
                                                                 =
                                                                 let uu____78587
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____78588
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____78587,
                                                                   uu____78588)
                                                                  in
                                                               (match uu____78582
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____78590
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____78590
                                                                    then
                                                                    let uu____78595
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____78597
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____78599
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____78601
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____78595
                                                                    uu____78597
                                                                    uu____78599
                                                                    uu____78601
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____78606
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___3152_78614
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___3152_78614.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___3152_78614.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___3152_78614.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___3152_78614.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___3152_78614.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___3152_78614.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___3152_78614.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___3152_78614.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____78616
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____78616
                                                                    then
                                                                    let uu____78621
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____78621
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____78626 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____78638 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____78638 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____78646 =
                                             let uu____78647 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____78647.FStar_Syntax_Syntax.n
                                              in
                                           match uu____78646 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____78652 -> false  in
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
                                          | uu____78655 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____78658 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___3172_78694 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___3172_78694.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___3172_78694.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___3172_78694.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___3172_78694.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___3172_78694.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___3172_78694.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___3172_78694.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___3172_78694.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____78770 = destruct_flex_t scrutinee wl1  in
             match uu____78770 with
             | ((_t,uv,_args),wl2) ->
                 let uu____78781 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____78781 with
                  | (xs,pat_term,uu____78797,uu____78798) ->
                      let uu____78803 =
                        FStar_List.fold_left
                          (fun uu____78826  ->
                             fun x  ->
                               match uu____78826 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____78847 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____78847 with
                                    | (uu____78866,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____78803 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____78887 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____78887 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___3212_78904 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___3212_78904.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___3212_78904.umax_heuristic_ok);
                                    tcenv = (uu___3212_78904.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____78916 = solve env1 wl'  in
                                (match uu____78916 with
                                 | Success (uu____78919,imps) ->
                                     let wl'1 =
                                       let uu___3220_78922 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___3220_78922.wl_deferred);
                                         ctr = (uu___3220_78922.ctr);
                                         defer_ok =
                                           (uu___3220_78922.defer_ok);
                                         smt_ok = (uu___3220_78922.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___3220_78922.umax_heuristic_ok);
                                         tcenv = (uu___3220_78922.tcenv);
                                         wl_implicits =
                                           (uu___3220_78922.wl_implicits)
                                       }  in
                                     let uu____78923 = solve env1 wl'1  in
                                     (match uu____78923 with
                                      | Success (uu____78926,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___3228_78930 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___3228_78930.attempting);
                                                 wl_deferred =
                                                   (uu___3228_78930.wl_deferred);
                                                 ctr = (uu___3228_78930.ctr);
                                                 defer_ok =
                                                   (uu___3228_78930.defer_ok);
                                                 smt_ok =
                                                   (uu___3228_78930.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3228_78930.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3228_78930.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____78931 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____78938 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____78961 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____78961
                 then
                   let uu____78966 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____78968 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____78966 uu____78968
                 else ());
                (let uu____78973 =
                   let uu____78994 =
                     let uu____79003 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____79003)  in
                   let uu____79010 =
                     let uu____79019 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____79019)  in
                   (uu____78994, uu____79010)  in
                 match uu____78973 with
                 | ((uu____79049,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____79052;
                                   FStar_Syntax_Syntax.vars = uu____79053;_}),
                    (s,t)) ->
                     let uu____79124 =
                       let uu____79126 = is_flex scrutinee  in
                       Prims.op_Negation uu____79126  in
                     if uu____79124
                     then
                       ((let uu____79137 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____79137
                         then
                           let uu____79142 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____79142
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____79161 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____79161
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____79176 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____79176
                           then
                             let uu____79181 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____79183 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____79181 uu____79183
                           else ());
                          (let pat_discriminates uu___613_79208 =
                             match uu___613_79208 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____79224;
                                  FStar_Syntax_Syntax.p = uu____79225;_},FStar_Pervasives_Native.None
                                ,uu____79226) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____79240;
                                  FStar_Syntax_Syntax.p = uu____79241;_},FStar_Pervasives_Native.None
                                ,uu____79242) -> true
                             | uu____79269 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____79372 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____79372 with
                                       | (uu____79374,uu____79375,t') ->
                                           let uu____79393 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____79393 with
                                            | (FullMatch ,uu____79405) ->
                                                true
                                            | (HeadMatch
                                               uu____79419,uu____79420) ->
                                                true
                                            | uu____79435 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____79472 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____79472
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____79483 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____79483 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____79571,uu____79572) ->
                                       branches1
                                   | uu____79717 -> branches  in
                                 let uu____79772 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____79781 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____79781 with
                                        | (p,uu____79785,uu____79786) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _79815  -> FStar_Util.Inr _79815)
                                   uu____79772))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____79845 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____79845 with
                                | (p,uu____79854,e) ->
                                    ((let uu____79873 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____79873
                                      then
                                        let uu____79878 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____79880 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____79878 uu____79880
                                      else ());
                                     (let uu____79885 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _79900  -> FStar_Util.Inr _79900)
                                        uu____79885)))))
                 | ((s,t),(uu____79903,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____79906;
                                         FStar_Syntax_Syntax.vars =
                                           uu____79907;_}))
                     ->
                     let uu____79976 =
                       let uu____79978 = is_flex scrutinee  in
                       Prims.op_Negation uu____79978  in
                     if uu____79976
                     then
                       ((let uu____79989 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____79989
                         then
                           let uu____79994 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____79994
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____80013 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____80013
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____80028 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____80028
                           then
                             let uu____80033 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____80035 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____80033 uu____80035
                           else ());
                          (let pat_discriminates uu___613_80060 =
                             match uu___613_80060 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____80076;
                                  FStar_Syntax_Syntax.p = uu____80077;_},FStar_Pervasives_Native.None
                                ,uu____80078) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____80092;
                                  FStar_Syntax_Syntax.p = uu____80093;_},FStar_Pervasives_Native.None
                                ,uu____80094) -> true
                             | uu____80121 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____80224 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____80224 with
                                       | (uu____80226,uu____80227,t') ->
                                           let uu____80245 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____80245 with
                                            | (FullMatch ,uu____80257) ->
                                                true
                                            | (HeadMatch
                                               uu____80271,uu____80272) ->
                                                true
                                            | uu____80287 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____80324 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____80324
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____80335 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____80335 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____80423,uu____80424) ->
                                       branches1
                                   | uu____80569 -> branches  in
                                 let uu____80624 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____80633 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____80633 with
                                        | (p,uu____80637,uu____80638) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _80667  -> FStar_Util.Inr _80667)
                                   uu____80624))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____80697 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____80697 with
                                | (p,uu____80706,e) ->
                                    ((let uu____80725 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____80725
                                      then
                                        let uu____80730 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____80732 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____80730 uu____80732
                                      else ());
                                     (let uu____80737 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _80752  -> FStar_Util.Inr _80752)
                                        uu____80737)))))
                 | uu____80753 ->
                     ((let uu____80775 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____80775
                       then
                         let uu____80780 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____80782 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____80780 uu____80782
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____80828 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____80828
            then
              let uu____80833 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____80835 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____80837 = FStar_Syntax_Print.term_to_string t1  in
              let uu____80839 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____80833 uu____80835 uu____80837 uu____80839
            else ());
           (let uu____80844 = head_matches_delta env1 wl1 t1 t2  in
            match uu____80844 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____80875,uu____80876) ->
                     let rec may_relate head3 =
                       let uu____80904 =
                         let uu____80905 = FStar_Syntax_Subst.compress head3
                            in
                         uu____80905.FStar_Syntax_Syntax.n  in
                       match uu____80904 with
                       | FStar_Syntax_Syntax.Tm_name uu____80909 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____80911 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____80936 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____80936 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____80938 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____80941
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____80942 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____80945,uu____80946) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____80988) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____80994) ->
                           may_relate t
                       | uu____80999 -> false  in
                     let uu____81001 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____81001 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____81022 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____81022
                          then
                            let uu____81025 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____81025 with
                             | (guard,wl2) ->
                                 let uu____81032 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____81032)
                          else
                            (let uu____81035 =
                               let uu____81037 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____81039 =
                                 let uu____81041 =
                                   let uu____81045 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____81045
                                     (fun x  ->
                                        let uu____81052 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____81052)
                                    in
                                 FStar_Util.dflt "" uu____81041  in
                               let uu____81057 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____81059 =
                                 let uu____81061 =
                                   let uu____81065 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____81065
                                     (fun x  ->
                                        let uu____81072 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____81072)
                                    in
                                 FStar_Util.dflt "" uu____81061  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____81037 uu____81039 uu____81057
                                 uu____81059
                                in
                             giveup env1 uu____81035 orig))
                 | (HeadMatch (true ),uu____81078) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____81093 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____81093 with
                        | (guard,wl2) ->
                            let uu____81100 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____81100)
                     else
                       (let uu____81103 =
                          let uu____81105 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____81107 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____81105 uu____81107
                           in
                        giveup env1 uu____81103 orig)
                 | (uu____81110,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___3401_81124 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___3401_81124.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___3401_81124.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___3401_81124.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___3401_81124.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___3401_81124.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___3401_81124.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___3401_81124.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___3401_81124.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____81151 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____81151
          then
            let uu____81154 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____81154
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____81160 =
                let uu____81163 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____81163  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____81160 t1);
             (let uu____81182 =
                let uu____81185 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____81185  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____81182 t2);
             (let uu____81204 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____81204
              then
                let uu____81208 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____81210 =
                  let uu____81212 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____81214 =
                    let uu____81216 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____81216  in
                  Prims.op_Hat uu____81212 uu____81214  in
                let uu____81219 =
                  let uu____81221 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____81223 =
                    let uu____81225 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____81225  in
                  Prims.op_Hat uu____81221 uu____81223  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____81208 uu____81210 uu____81219
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____81232,uu____81233) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____81257,FStar_Syntax_Syntax.Tm_delayed uu____81258) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____81282,uu____81283) ->
                  let uu____81310 =
                    let uu___3432_81311 = problem  in
                    let uu____81312 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3432_81311.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____81312;
                      FStar_TypeChecker_Common.relation =
                        (uu___3432_81311.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3432_81311.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3432_81311.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3432_81311.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3432_81311.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3432_81311.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3432_81311.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3432_81311.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____81310 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____81313,uu____81314) ->
                  let uu____81321 =
                    let uu___3438_81322 = problem  in
                    let uu____81323 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3438_81322.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____81323;
                      FStar_TypeChecker_Common.relation =
                        (uu___3438_81322.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3438_81322.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3438_81322.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3438_81322.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3438_81322.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3438_81322.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3438_81322.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3438_81322.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____81321 wl
              | (uu____81324,FStar_Syntax_Syntax.Tm_ascribed uu____81325) ->
                  let uu____81352 =
                    let uu___3444_81353 = problem  in
                    let uu____81354 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3444_81353.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3444_81353.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3444_81353.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____81354;
                      FStar_TypeChecker_Common.element =
                        (uu___3444_81353.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3444_81353.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3444_81353.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3444_81353.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3444_81353.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3444_81353.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____81352 wl
              | (uu____81355,FStar_Syntax_Syntax.Tm_meta uu____81356) ->
                  let uu____81363 =
                    let uu___3450_81364 = problem  in
                    let uu____81365 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3450_81364.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3450_81364.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3450_81364.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____81365;
                      FStar_TypeChecker_Common.element =
                        (uu___3450_81364.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3450_81364.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3450_81364.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3450_81364.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3450_81364.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3450_81364.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____81363 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____81367),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____81369)) ->
                  let uu____81378 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____81378
              | (FStar_Syntax_Syntax.Tm_bvar uu____81379,uu____81380) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____81382,FStar_Syntax_Syntax.Tm_bvar uu____81383) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___614_81453 =
                    match uu___614_81453 with
                    | [] -> c
                    | bs ->
                        let uu____81481 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____81481
                     in
                  let uu____81492 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____81492 with
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
                                    let uu____81641 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____81641
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
                  let mk_t t l uu___615_81730 =
                    match uu___615_81730 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____81772 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____81772 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____81917 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____81918 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____81917
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____81918 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____81920,uu____81921) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____81952 -> true
                    | uu____81972 -> false  in
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
                      (let uu____82032 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_82040 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_82040.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_82040.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_82040.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_82040.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_82040.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_82040.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_82040.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_82040.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_82040.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_82040.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_82040.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_82040.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_82040.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_82040.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_82040.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_82040.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_82040.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_82040.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_82040.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_82040.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_82040.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_82040.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_82040.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_82040.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_82040.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_82040.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_82040.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_82040.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_82040.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_82040.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_82040.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_82040.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_82040.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_82040.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_82040.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_82040.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_82040.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_82040.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_82040.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_82040.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____82032 with
                       | (uu____82045,ty,uu____82047) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____82056 =
                                 let uu____82057 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____82057.FStar_Syntax_Syntax.n  in
                               match uu____82056 with
                               | FStar_Syntax_Syntax.Tm_refine uu____82060 ->
                                   let uu____82067 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____82067
                               | uu____82068 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____82071 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____82071
                             then
                               let uu____82076 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____82078 =
                                 let uu____82080 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____82080
                                  in
                               let uu____82081 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____82076 uu____82078 uu____82081
                             else ());
                            r1))
                     in
                  let uu____82086 =
                    let uu____82103 = maybe_eta t1  in
                    let uu____82110 = maybe_eta t2  in
                    (uu____82103, uu____82110)  in
                  (match uu____82086 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_82152 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_82152.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_82152.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_82152.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_82152.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_82152.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_82152.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_82152.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_82152.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____82173 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____82173
                       then
                         let uu____82176 = destruct_flex_t not_abs wl  in
                         (match uu____82176 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_82193 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_82193.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_82193.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_82193.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_82193.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_82193.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_82193.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_82193.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_82193.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____82217 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____82217
                       then
                         let uu____82220 = destruct_flex_t not_abs wl  in
                         (match uu____82220 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_82237 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_82237.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_82237.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_82237.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_82237.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_82237.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_82237.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_82237.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_82237.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____82241 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____82259,FStar_Syntax_Syntax.Tm_abs uu____82260) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____82291 -> true
                    | uu____82311 -> false  in
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
                      (let uu____82371 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_82379 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_82379.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_82379.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_82379.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_82379.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_82379.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_82379.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_82379.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_82379.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_82379.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_82379.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_82379.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_82379.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_82379.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_82379.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_82379.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_82379.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_82379.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_82379.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_82379.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_82379.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_82379.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_82379.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_82379.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_82379.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_82379.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_82379.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_82379.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_82379.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_82379.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_82379.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_82379.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_82379.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_82379.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_82379.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_82379.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_82379.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_82379.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_82379.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_82379.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_82379.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____82371 with
                       | (uu____82384,ty,uu____82386) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____82395 =
                                 let uu____82396 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____82396.FStar_Syntax_Syntax.n  in
                               match uu____82395 with
                               | FStar_Syntax_Syntax.Tm_refine uu____82399 ->
                                   let uu____82406 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____82406
                               | uu____82407 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____82410 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____82410
                             then
                               let uu____82415 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____82417 =
                                 let uu____82419 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____82419
                                  in
                               let uu____82420 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____82415 uu____82417 uu____82420
                             else ());
                            r1))
                     in
                  let uu____82425 =
                    let uu____82442 = maybe_eta t1  in
                    let uu____82449 = maybe_eta t2  in
                    (uu____82442, uu____82449)  in
                  (match uu____82425 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_82491 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_82491.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_82491.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_82491.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_82491.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_82491.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_82491.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_82491.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_82491.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____82512 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____82512
                       then
                         let uu____82515 = destruct_flex_t not_abs wl  in
                         (match uu____82515 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_82532 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_82532.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_82532.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_82532.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_82532.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_82532.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_82532.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_82532.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_82532.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____82556 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____82556
                       then
                         let uu____82559 = destruct_flex_t not_abs wl  in
                         (match uu____82559 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_82576 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_82576.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_82576.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_82576.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_82576.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_82576.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_82576.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_82576.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_82576.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____82580 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____82610 =
                    let uu____82615 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____82615 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3613_82643 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_82643.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_82643.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_82645 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_82645.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_82645.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____82646,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3613_82661 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_82661.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_82661.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_82663 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_82663.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_82663.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____82664 -> (x1, x2)  in
                  (match uu____82610 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____82683 = as_refinement false env t11  in
                       (match uu____82683 with
                        | (x12,phi11) ->
                            let uu____82691 = as_refinement false env t21  in
                            (match uu____82691 with
                             | (x22,phi21) ->
                                 ((let uu____82700 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____82700
                                   then
                                     ((let uu____82705 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____82707 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____82709 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____82705
                                         uu____82707 uu____82709);
                                      (let uu____82712 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____82714 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____82716 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____82712
                                         uu____82714 uu____82716))
                                   else ());
                                  (let uu____82721 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____82721 with
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
                                         let uu____82792 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____82792
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____82804 =
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
                                         (let uu____82817 =
                                            let uu____82820 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____82820
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____82817
                                            (p_guard base_prob));
                                         (let uu____82839 =
                                            let uu____82842 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____82842
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____82839
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____82861 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____82861)
                                          in
                                       let has_uvars =
                                         (let uu____82866 =
                                            let uu____82868 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____82868
                                             in
                                          Prims.op_Negation uu____82866) ||
                                           (let uu____82872 =
                                              let uu____82874 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____82874
                                               in
                                            Prims.op_Negation uu____82872)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____82878 =
                                           let uu____82883 =
                                             let uu____82892 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____82892]  in
                                           mk_t_problem wl1 uu____82883 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____82878 with
                                          | (ref_prob,wl2) ->
                                              let uu____82914 =
                                                solve env1
                                                  (let uu___3657_82916 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3657_82916.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3657_82916.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3657_82916.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3657_82916.tcenv);
                                                     wl_implicits =
                                                       (uu___3657_82916.wl_implicits)
                                                   })
                                                 in
                                              (match uu____82914 with
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
                                               | Success uu____82933 ->
                                                   let guard =
                                                     let uu____82941 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____82941
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3668_82950 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3668_82950.attempting);
                                                       wl_deferred =
                                                         (uu___3668_82950.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___3668_82950.defer_ok);
                                                       smt_ok =
                                                         (uu___3668_82950.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3668_82950.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3668_82950.tcenv);
                                                       wl_implicits =
                                                         (uu___3668_82950.wl_implicits)
                                                     }  in
                                                   let uu____82952 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____82952))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82955,FStar_Syntax_Syntax.Tm_uvar uu____82956) ->
                  let uu____82981 = destruct_flex_t t1 wl  in
                  (match uu____82981 with
                   | (f1,wl1) ->
                       let uu____82988 = destruct_flex_t t2 wl1  in
                       (match uu____82988 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82995;
                    FStar_Syntax_Syntax.pos = uu____82996;
                    FStar_Syntax_Syntax.vars = uu____82997;_},uu____82998),FStar_Syntax_Syntax.Tm_uvar
                 uu____82999) ->
                  let uu____83048 = destruct_flex_t t1 wl  in
                  (match uu____83048 with
                   | (f1,wl1) ->
                       let uu____83055 = destruct_flex_t t2 wl1  in
                       (match uu____83055 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____83062,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____83063;
                    FStar_Syntax_Syntax.pos = uu____83064;
                    FStar_Syntax_Syntax.vars = uu____83065;_},uu____83066))
                  ->
                  let uu____83115 = destruct_flex_t t1 wl  in
                  (match uu____83115 with
                   | (f1,wl1) ->
                       let uu____83122 = destruct_flex_t t2 wl1  in
                       (match uu____83122 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____83129;
                    FStar_Syntax_Syntax.pos = uu____83130;
                    FStar_Syntax_Syntax.vars = uu____83131;_},uu____83132),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____83133;
                    FStar_Syntax_Syntax.pos = uu____83134;
                    FStar_Syntax_Syntax.vars = uu____83135;_},uu____83136))
                  ->
                  let uu____83209 = destruct_flex_t t1 wl  in
                  (match uu____83209 with
                   | (f1,wl1) ->
                       let uu____83216 = destruct_flex_t t2 wl1  in
                       (match uu____83216 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____83223,uu____83224) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____83237 = destruct_flex_t t1 wl  in
                  (match uu____83237 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____83244;
                    FStar_Syntax_Syntax.pos = uu____83245;
                    FStar_Syntax_Syntax.vars = uu____83246;_},uu____83247),uu____83248)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____83285 = destruct_flex_t t1 wl  in
                  (match uu____83285 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____83292,FStar_Syntax_Syntax.Tm_uvar uu____83293) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____83306,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____83307;
                    FStar_Syntax_Syntax.pos = uu____83308;
                    FStar_Syntax_Syntax.vars = uu____83309;_},uu____83310))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____83347,FStar_Syntax_Syntax.Tm_arrow uu____83348) ->
                  solve_t' env
                    (let uu___3768_83376 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_83376.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_83376.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_83376.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_83376.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_83376.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_83376.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_83376.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_83376.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_83376.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____83377;
                    FStar_Syntax_Syntax.pos = uu____83378;
                    FStar_Syntax_Syntax.vars = uu____83379;_},uu____83380),FStar_Syntax_Syntax.Tm_arrow
                 uu____83381) ->
                  solve_t' env
                    (let uu___3768_83433 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_83433.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_83433.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_83433.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_83433.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_83433.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_83433.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_83433.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_83433.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_83433.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____83434,FStar_Syntax_Syntax.Tm_uvar uu____83435) ->
                  let uu____83448 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____83448
              | (uu____83449,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____83450;
                    FStar_Syntax_Syntax.pos = uu____83451;
                    FStar_Syntax_Syntax.vars = uu____83452;_},uu____83453))
                  ->
                  let uu____83490 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____83490
              | (FStar_Syntax_Syntax.Tm_uvar uu____83491,uu____83492) ->
                  let uu____83505 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____83505
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____83506;
                    FStar_Syntax_Syntax.pos = uu____83507;
                    FStar_Syntax_Syntax.vars = uu____83508;_},uu____83509),uu____83510)
                  ->
                  let uu____83547 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____83547
              | (FStar_Syntax_Syntax.Tm_refine uu____83548,uu____83549) ->
                  let t21 =
                    let uu____83557 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____83557  in
                  solve_t env
                    (let uu___3803_83583 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3803_83583.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3803_83583.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3803_83583.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3803_83583.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3803_83583.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3803_83583.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3803_83583.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3803_83583.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3803_83583.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____83584,FStar_Syntax_Syntax.Tm_refine uu____83585) ->
                  let t11 =
                    let uu____83593 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____83593  in
                  solve_t env
                    (let uu___3810_83619 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3810_83619.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3810_83619.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3810_83619.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3810_83619.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3810_83619.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3810_83619.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3810_83619.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3810_83619.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3810_83619.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____83701 =
                    let uu____83702 = guard_of_prob env wl problem t1 t2  in
                    match uu____83702 with
                    | (guard,wl1) ->
                        let uu____83709 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____83709
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____83928 = br1  in
                        (match uu____83928 with
                         | (p1,w1,uu____83957) ->
                             let uu____83974 = br2  in
                             (match uu____83974 with
                              | (p2,w2,uu____83997) ->
                                  let uu____84002 =
                                    let uu____84004 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____84004  in
                                  if uu____84002
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____84031 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____84031 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____84068 = br2  in
                                         (match uu____84068 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____84101 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____84101
                                                 in
                                              let uu____84106 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____84137,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____84158) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____84217 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____84217 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____84106
                                                (fun uu____84289  ->
                                                   match uu____84289 with
                                                   | (wprobs,wl2) ->
                                                       let uu____84326 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____84326
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____84347
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____84347
                                                              then
                                                                let uu____84352
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____84354
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____84352
                                                                  uu____84354
                                                              else ());
                                                             (let uu____84360
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____84360
                                                                (fun
                                                                   uu____84396
                                                                    ->
                                                                   match uu____84396
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
                    | uu____84525 -> FStar_Pervasives_Native.None  in
                  let uu____84566 = solve_branches wl brs1 brs2  in
                  (match uu____84566 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____84617 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____84617 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____84651 =
                                FStar_List.map
                                  (fun uu____84663  ->
                                     match uu____84663 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____84651  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____84672 =
                              let uu____84673 =
                                let uu____84674 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____84674
                                  (let uu___3909_84682 = wl3  in
                                   {
                                     attempting =
                                       (uu___3909_84682.attempting);
                                     wl_deferred =
                                       (uu___3909_84682.wl_deferred);
                                     ctr = (uu___3909_84682.ctr);
                                     defer_ok = (uu___3909_84682.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3909_84682.umax_heuristic_ok);
                                     tcenv = (uu___3909_84682.tcenv);
                                     wl_implicits =
                                       (uu___3909_84682.wl_implicits)
                                   })
                                 in
                              solve env uu____84673  in
                            (match uu____84672 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____84687 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____84694,uu____84695) ->
                  let head1 =
                    let uu____84719 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84719
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84765 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84765
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84811 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84811
                    then
                      let uu____84815 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84817 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84819 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84815 uu____84817 uu____84819
                    else ());
                   (let no_free_uvars t =
                      (let uu____84833 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84833) &&
                        (let uu____84837 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84837)
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
                      let uu____84854 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84854 = FStar_Syntax_Util.Equal  in
                    let uu____84855 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84855
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84859 = equal t1 t2  in
                         (if uu____84859
                          then
                            let uu____84862 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84862
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84867 =
                            let uu____84874 = equal t1 t2  in
                            if uu____84874
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84887 = mk_eq2 wl env orig t1 t2  in
                               match uu____84887 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84867 with
                          | (guard,wl1) ->
                              let uu____84908 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84908))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____84911,uu____84912) ->
                  let head1 =
                    let uu____84920 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84920
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84966 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84966
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85012 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85012
                    then
                      let uu____85016 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85018 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85020 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85016 uu____85018 uu____85020
                    else ());
                   (let no_free_uvars t =
                      (let uu____85034 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85034) &&
                        (let uu____85038 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85038)
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
                      let uu____85055 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85055 = FStar_Syntax_Util.Equal  in
                    let uu____85056 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85056
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85060 = equal t1 t2  in
                         (if uu____85060
                          then
                            let uu____85063 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85063
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85068 =
                            let uu____85075 = equal t1 t2  in
                            if uu____85075
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85088 = mk_eq2 wl env orig t1 t2  in
                               match uu____85088 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85068 with
                          | (guard,wl1) ->
                              let uu____85109 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85109))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____85112,uu____85113) ->
                  let head1 =
                    let uu____85115 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85115
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85161 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85161
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85207 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85207
                    then
                      let uu____85211 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85213 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85215 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85211 uu____85213 uu____85215
                    else ());
                   (let no_free_uvars t =
                      (let uu____85229 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85229) &&
                        (let uu____85233 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85233)
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
                      let uu____85250 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85250 = FStar_Syntax_Util.Equal  in
                    let uu____85251 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85251
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85255 = equal t1 t2  in
                         (if uu____85255
                          then
                            let uu____85258 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85258
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85263 =
                            let uu____85270 = equal t1 t2  in
                            if uu____85270
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85283 = mk_eq2 wl env orig t1 t2  in
                               match uu____85283 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85263 with
                          | (guard,wl1) ->
                              let uu____85304 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85304))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____85307,uu____85308) ->
                  let head1 =
                    let uu____85310 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85310
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85356 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85356
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85402 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85402
                    then
                      let uu____85406 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85408 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85410 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85406 uu____85408 uu____85410
                    else ());
                   (let no_free_uvars t =
                      (let uu____85424 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85424) &&
                        (let uu____85428 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85428)
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
                      let uu____85445 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85445 = FStar_Syntax_Util.Equal  in
                    let uu____85446 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85446
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85450 = equal t1 t2  in
                         (if uu____85450
                          then
                            let uu____85453 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85453
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85458 =
                            let uu____85465 = equal t1 t2  in
                            if uu____85465
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85478 = mk_eq2 wl env orig t1 t2  in
                               match uu____85478 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85458 with
                          | (guard,wl1) ->
                              let uu____85499 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85499))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____85502,uu____85503) ->
                  let head1 =
                    let uu____85505 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85505
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85551 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85551
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85597 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85597
                    then
                      let uu____85601 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85603 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85605 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85601 uu____85603 uu____85605
                    else ());
                   (let no_free_uvars t =
                      (let uu____85619 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85619) &&
                        (let uu____85623 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85623)
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
                      let uu____85640 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85640 = FStar_Syntax_Util.Equal  in
                    let uu____85641 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85641
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85645 = equal t1 t2  in
                         (if uu____85645
                          then
                            let uu____85648 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85648
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85653 =
                            let uu____85660 = equal t1 t2  in
                            if uu____85660
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85673 = mk_eq2 wl env orig t1 t2  in
                               match uu____85673 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85653 with
                          | (guard,wl1) ->
                              let uu____85694 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85694))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____85697,uu____85698) ->
                  let head1 =
                    let uu____85716 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85716
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85762 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85762
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85808 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85808
                    then
                      let uu____85812 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85814 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85816 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85812 uu____85814 uu____85816
                    else ());
                   (let no_free_uvars t =
                      (let uu____85830 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85830) &&
                        (let uu____85834 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85834)
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
                      let uu____85851 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85851 = FStar_Syntax_Util.Equal  in
                    let uu____85852 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85852
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85856 = equal t1 t2  in
                         (if uu____85856
                          then
                            let uu____85859 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85859
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85864 =
                            let uu____85871 = equal t1 t2  in
                            if uu____85871
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85884 = mk_eq2 wl env orig t1 t2  in
                               match uu____85884 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85864 with
                          | (guard,wl1) ->
                              let uu____85905 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85905))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85908,FStar_Syntax_Syntax.Tm_match uu____85909) ->
                  let head1 =
                    let uu____85933 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85933
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85979 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85979
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____86025 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____86025
                    then
                      let uu____86029 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____86031 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____86033 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____86029 uu____86031 uu____86033
                    else ());
                   (let no_free_uvars t =
                      (let uu____86047 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86047) &&
                        (let uu____86051 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86051)
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
                      let uu____86068 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____86068 = FStar_Syntax_Util.Equal  in
                    let uu____86069 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____86069
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____86073 = equal t1 t2  in
                         (if uu____86073
                          then
                            let uu____86076 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____86076
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____86081 =
                            let uu____86088 = equal t1 t2  in
                            if uu____86088
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____86101 = mk_eq2 wl env orig t1 t2  in
                               match uu____86101 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____86081 with
                          | (guard,wl1) ->
                              let uu____86122 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____86122))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____86125,FStar_Syntax_Syntax.Tm_uinst uu____86126) ->
                  let head1 =
                    let uu____86134 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____86134
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____86174 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____86174
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____86214 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____86214
                    then
                      let uu____86218 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____86220 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____86222 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____86218 uu____86220 uu____86222
                    else ());
                   (let no_free_uvars t =
                      (let uu____86236 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86236) &&
                        (let uu____86240 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86240)
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
                      let uu____86257 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____86257 = FStar_Syntax_Util.Equal  in
                    let uu____86258 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____86258
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____86262 = equal t1 t2  in
                         (if uu____86262
                          then
                            let uu____86265 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____86265
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____86270 =
                            let uu____86277 = equal t1 t2  in
                            if uu____86277
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____86290 = mk_eq2 wl env orig t1 t2  in
                               match uu____86290 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____86270 with
                          | (guard,wl1) ->
                              let uu____86311 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____86311))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____86314,FStar_Syntax_Syntax.Tm_name uu____86315) ->
                  let head1 =
                    let uu____86317 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____86317
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____86357 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____86357
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____86397 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____86397
                    then
                      let uu____86401 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____86403 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____86405 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____86401 uu____86403 uu____86405
                    else ());
                   (let no_free_uvars t =
                      (let uu____86419 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86419) &&
                        (let uu____86423 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86423)
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
                      let uu____86440 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____86440 = FStar_Syntax_Util.Equal  in
                    let uu____86441 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____86441
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____86445 = equal t1 t2  in
                         (if uu____86445
                          then
                            let uu____86448 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____86448
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____86453 =
                            let uu____86460 = equal t1 t2  in
                            if uu____86460
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____86473 = mk_eq2 wl env orig t1 t2  in
                               match uu____86473 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____86453 with
                          | (guard,wl1) ->
                              let uu____86494 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____86494))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____86497,FStar_Syntax_Syntax.Tm_constant uu____86498) ->
                  let head1 =
                    let uu____86500 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____86500
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____86540 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____86540
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____86580 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____86580
                    then
                      let uu____86584 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____86586 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____86588 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____86584 uu____86586 uu____86588
                    else ());
                   (let no_free_uvars t =
                      (let uu____86602 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86602) &&
                        (let uu____86606 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86606)
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
                      let uu____86623 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____86623 = FStar_Syntax_Util.Equal  in
                    let uu____86624 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____86624
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____86628 = equal t1 t2  in
                         (if uu____86628
                          then
                            let uu____86631 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____86631
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____86636 =
                            let uu____86643 = equal t1 t2  in
                            if uu____86643
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____86656 = mk_eq2 wl env orig t1 t2  in
                               match uu____86656 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____86636 with
                          | (guard,wl1) ->
                              let uu____86677 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____86677))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____86680,FStar_Syntax_Syntax.Tm_fvar uu____86681) ->
                  let head1 =
                    let uu____86683 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____86683
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____86723 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____86723
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____86763 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____86763
                    then
                      let uu____86767 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____86769 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____86771 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____86767 uu____86769 uu____86771
                    else ());
                   (let no_free_uvars t =
                      (let uu____86785 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86785) &&
                        (let uu____86789 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86789)
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
                      let uu____86806 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____86806 = FStar_Syntax_Util.Equal  in
                    let uu____86807 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____86807
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____86811 = equal t1 t2  in
                         (if uu____86811
                          then
                            let uu____86814 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____86814
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____86819 =
                            let uu____86826 = equal t1 t2  in
                            if uu____86826
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____86839 = mk_eq2 wl env orig t1 t2  in
                               match uu____86839 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____86819 with
                          | (guard,wl1) ->
                              let uu____86860 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____86860))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____86863,FStar_Syntax_Syntax.Tm_app uu____86864) ->
                  let head1 =
                    let uu____86882 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____86882
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____86922 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____86922
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____86962 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____86962
                    then
                      let uu____86966 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____86968 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____86970 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____86966 uu____86968 uu____86970
                    else ());
                   (let no_free_uvars t =
                      (let uu____86984 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86984) &&
                        (let uu____86988 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86988)
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
                      let uu____87005 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____87005 = FStar_Syntax_Util.Equal  in
                    let uu____87006 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____87006
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____87010 = equal t1 t2  in
                         (if uu____87010
                          then
                            let uu____87013 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____87013
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____87018 =
                            let uu____87025 = equal t1 t2  in
                            if uu____87025
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____87038 = mk_eq2 wl env orig t1 t2  in
                               match uu____87038 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____87018 with
                          | (guard,wl1) ->
                              let uu____87059 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____87059))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____87062,FStar_Syntax_Syntax.Tm_let uu____87063) ->
                  let uu____87090 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____87090
                  then
                    let uu____87093 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____87093
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____87097,uu____87098) ->
                  let uu____87112 =
                    let uu____87118 =
                      let uu____87120 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____87122 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____87124 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____87126 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____87120 uu____87122 uu____87124 uu____87126
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____87118)
                     in
                  FStar_Errors.raise_error uu____87112
                    t1.FStar_Syntax_Syntax.pos
              | (uu____87130,FStar_Syntax_Syntax.Tm_let uu____87131) ->
                  let uu____87145 =
                    let uu____87151 =
                      let uu____87153 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____87155 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____87157 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____87159 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____87153 uu____87155 uu____87157 uu____87159
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____87151)
                     in
                  FStar_Errors.raise_error uu____87145
                    t1.FStar_Syntax_Syntax.pos
              | uu____87163 -> giveup env "head tag mismatch" orig))))

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
          (let uu____87227 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____87227
           then
             let uu____87232 =
               let uu____87234 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____87234  in
             let uu____87235 =
               let uu____87237 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____87237  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____87232 uu____87235
           else ());
          (let uu____87241 =
             let uu____87243 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____87243  in
           if uu____87241
           then
             let uu____87246 =
               let uu____87248 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____87250 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____87248 uu____87250
                in
             giveup env uu____87246 orig
           else
             (let uu____87255 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____87255 with
              | (ret_sub_prob,wl1) ->
                  let uu____87263 =
                    FStar_List.fold_right2
                      (fun uu____87300  ->
                         fun uu____87301  ->
                           fun uu____87302  ->
                             match (uu____87300, uu____87301, uu____87302)
                             with
                             | ((a1,uu____87346),(a2,uu____87348),(arg_sub_probs,wl2))
                                 ->
                                 let uu____87381 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____87381 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____87263 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____87411 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____87411  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____87419 = attempt sub_probs wl3  in
                       solve env uu____87419)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____87442 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____87445)::[] -> wp1
              | uu____87470 ->
                  let uu____87481 =
                    let uu____87483 =
                      let uu____87485 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____87485  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____87483
                     in
                  failwith uu____87481
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____87492 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____87492]
              | x -> x  in
            let uu____87494 =
              let uu____87505 =
                let uu____87514 =
                  let uu____87515 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____87515 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____87514  in
              [uu____87505]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____87494;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____87533 = lift_c1 ()  in solve_eq uu____87533 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___616_87542  ->
                       match uu___616_87542 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____87547 -> false))
                in
             let uu____87549 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____87579)::uu____87580,(wp2,uu____87582)::uu____87583)
                   -> (wp1, wp2)
               | uu____87656 ->
                   let uu____87681 =
                     let uu____87687 =
                       let uu____87689 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____87691 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____87689 uu____87691
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____87687)
                      in
                   FStar_Errors.raise_error uu____87681
                     env.FStar_TypeChecker_Env.range
                in
             match uu____87549 with
             | (wpc1,wpc2) ->
                 let uu____87701 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____87701
                 then
                   let uu____87706 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____87706 wl
                 else
                   (let uu____87710 =
                      let uu____87717 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____87717  in
                    match uu____87710 with
                    | (c2_decl,qualifiers) ->
                        let uu____87738 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____87738
                        then
                          let c1_repr =
                            let uu____87745 =
                              let uu____87746 =
                                let uu____87747 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____87747  in
                              let uu____87748 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____87746 uu____87748
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____87745
                             in
                          let c2_repr =
                            let uu____87750 =
                              let uu____87751 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____87752 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____87751 uu____87752
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____87750
                             in
                          let uu____87753 =
                            let uu____87758 =
                              let uu____87760 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____87762 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____87760 uu____87762
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____87758
                             in
                          (match uu____87753 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____87768 = attempt [prob] wl2  in
                               solve env uu____87768)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____87783 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____87783
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____87792 =
                                     let uu____87799 =
                                       let uu____87800 =
                                         let uu____87817 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____87820 =
                                           let uu____87831 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____87840 =
                                             let uu____87851 =
                                               let uu____87860 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____87860
                                                in
                                             [uu____87851]  in
                                           uu____87831 :: uu____87840  in
                                         (uu____87817, uu____87820)  in
                                       FStar_Syntax_Syntax.Tm_app uu____87800
                                        in
                                     FStar_Syntax_Syntax.mk uu____87799  in
                                   uu____87792 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____87909 =
                                    let uu____87916 =
                                      let uu____87917 =
                                        let uu____87934 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____87937 =
                                          let uu____87948 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____87957 =
                                            let uu____87968 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____87977 =
                                              let uu____87988 =
                                                let uu____87997 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____87997
                                                 in
                                              [uu____87988]  in
                                            uu____87968 :: uu____87977  in
                                          uu____87948 :: uu____87957  in
                                        (uu____87934, uu____87937)  in
                                      FStar_Syntax_Syntax.Tm_app uu____87917
                                       in
                                    FStar_Syntax_Syntax.mk uu____87916  in
                                  uu____87909 FStar_Pervasives_Native.None r)
                              in
                           (let uu____88051 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____88051
                            then
                              let uu____88056 =
                                let uu____88058 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____88058
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____88056
                            else ());
                           (let uu____88062 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____88062 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____88071 =
                                    let uu____88074 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _88077  ->
                                         FStar_Pervasives_Native.Some _88077)
                                      uu____88074
                                     in
                                  solve_prob orig uu____88071 [] wl1  in
                                let uu____88078 = attempt [base_prob] wl2  in
                                solve env uu____88078))))
           in
        let uu____88079 = FStar_Util.physical_equality c1 c2  in
        if uu____88079
        then
          let uu____88082 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____88082
        else
          ((let uu____88086 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____88086
            then
              let uu____88091 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____88093 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____88091
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____88093
            else ());
           (let uu____88098 =
              let uu____88107 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____88110 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____88107, uu____88110)  in
            match uu____88098 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____88128),FStar_Syntax_Syntax.Total
                    (t2,uu____88130)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____88147 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____88147 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____88149,FStar_Syntax_Syntax.Total uu____88150) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____88169),FStar_Syntax_Syntax.Total
                    (t2,uu____88171)) ->
                     let uu____88188 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____88188 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____88191),FStar_Syntax_Syntax.GTotal
                    (t2,uu____88193)) ->
                     let uu____88210 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____88210 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____88213),FStar_Syntax_Syntax.GTotal
                    (t2,uu____88215)) ->
                     let uu____88232 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____88232 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____88234,FStar_Syntax_Syntax.Comp uu____88235) ->
                     let uu____88244 =
                       let uu___4158_88247 = problem  in
                       let uu____88250 =
                         let uu____88251 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____88251
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_88247.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____88250;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_88247.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_88247.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_88247.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_88247.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_88247.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_88247.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_88247.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_88247.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____88244 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____88252,FStar_Syntax_Syntax.Comp uu____88253) ->
                     let uu____88262 =
                       let uu___4158_88265 = problem  in
                       let uu____88268 =
                         let uu____88269 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____88269
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_88265.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____88268;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_88265.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_88265.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_88265.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_88265.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_88265.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_88265.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_88265.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_88265.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____88262 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____88270,FStar_Syntax_Syntax.GTotal uu____88271) ->
                     let uu____88280 =
                       let uu___4170_88283 = problem  in
                       let uu____88286 =
                         let uu____88287 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____88287
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_88283.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_88283.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_88283.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____88286;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_88283.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_88283.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_88283.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_88283.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_88283.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_88283.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____88280 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____88288,FStar_Syntax_Syntax.Total uu____88289) ->
                     let uu____88298 =
                       let uu___4170_88301 = problem  in
                       let uu____88304 =
                         let uu____88305 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____88305
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_88301.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_88301.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_88301.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____88304;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_88301.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_88301.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_88301.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_88301.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_88301.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_88301.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____88298 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____88306,FStar_Syntax_Syntax.Comp uu____88307) ->
                     let uu____88308 =
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
                     if uu____88308
                     then
                       let uu____88311 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____88311 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____88318 =
                            let uu____88323 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____88323
                            then (c1_comp, c2_comp)
                            else
                              (let uu____88332 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____88333 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____88332, uu____88333))
                             in
                          match uu____88318 with
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
                           (let uu____88341 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____88341
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____88349 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____88349 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____88352 =
                                  let uu____88354 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____88356 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____88354 uu____88356
                                   in
                                giveup env uu____88352 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____88367 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____88367 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____88417 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____88417 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____88442 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____88473  ->
                match uu____88473 with
                | (u1,u2) ->
                    let uu____88481 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____88483 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____88481 uu____88483))
         in
      FStar_All.pipe_right uu____88442 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____88520,[])) when
          let uu____88547 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____88547 -> "{}"
      | uu____88550 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____88577 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____88577
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____88589 =
              FStar_List.map
                (fun uu____88602  ->
                   match uu____88602 with
                   | (uu____88609,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____88589 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____88620 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____88620 imps
  
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
                  let uu____88677 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____88677
                  then
                    let uu____88685 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____88687 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____88685
                      (rel_to_string rel) uu____88687
                  else "TOP"  in
                let uu____88693 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____88693 with
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
              let uu____88753 =
                let uu____88756 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _88759  -> FStar_Pervasives_Native.Some _88759)
                  uu____88756
                 in
              FStar_Syntax_Syntax.new_bv uu____88753 t1  in
            let uu____88760 =
              let uu____88765 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____88765
               in
            match uu____88760 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____88825 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____88825
         then
           let uu____88830 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____88830
         else ());
        (let uu____88837 =
           FStar_Util.record_time (fun uu____88844  -> solve env probs)  in
         match uu____88837 with
         | (sol,ms) ->
             ((let uu____88856 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____88856
               then
                 let uu____88861 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____88861
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____88874 =
                     FStar_Util.record_time
                       (fun uu____88881  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____88874 with
                    | ((),ms1) ->
                        ((let uu____88892 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____88892
                          then
                            let uu____88897 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____88897
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____88911 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____88911
                     then
                       let uu____88918 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____88918
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
          ((let uu____88945 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____88945
            then
              let uu____88950 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____88950
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____88957 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____88957
             then
               let uu____88962 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____88962
             else ());
            (let f2 =
               let uu____88968 =
                 let uu____88969 = FStar_Syntax_Util.unmeta f1  in
                 uu____88969.FStar_Syntax_Syntax.n  in
               match uu____88968 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____88973 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4286_88974 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___4286_88974.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___4286_88974.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___4286_88974.FStar_TypeChecker_Env.implicits)
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
            let uu____89029 =
              let uu____89030 =
                let uu____89031 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _89032  ->
                       FStar_TypeChecker_Common.NonTrivial _89032)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____89031;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____89030  in
            FStar_All.pipe_left
              (fun _89039  -> FStar_Pervasives_Native.Some _89039)
              uu____89029
  
let with_guard_no_simp :
  'Auu____89049 .
    'Auu____89049 ->
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
            let uu____89072 =
              let uu____89073 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _89074  -> FStar_TypeChecker_Common.NonTrivial _89074)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____89073;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____89072
  
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
          (let uu____89107 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____89107
           then
             let uu____89112 = FStar_Syntax_Print.term_to_string t1  in
             let uu____89114 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____89112
               uu____89114
           else ());
          (let uu____89119 =
             let uu____89124 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____89124
              in
           match uu____89119 with
           | (prob,wl) ->
               let g =
                 let uu____89132 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____89142  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____89132  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____89178 = try_teq true env t1 t2  in
        match uu____89178 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____89183 = FStar_TypeChecker_Env.get_range env  in
              let uu____89184 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____89183 uu____89184);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____89192 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____89192
              then
                let uu____89197 = FStar_Syntax_Print.term_to_string t1  in
                let uu____89199 = FStar_Syntax_Print.term_to_string t2  in
                let uu____89201 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____89197
                  uu____89199 uu____89201
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
          let uu____89227 = FStar_TypeChecker_Env.get_range env  in
          let uu____89228 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____89227 uu____89228
  
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
        (let uu____89257 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____89257
         then
           let uu____89262 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____89264 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____89262 uu____89264
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____89275 =
           let uu____89282 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____89282 "sub_comp"
            in
         match uu____89275 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____89295 =
                 FStar_Util.record_time
                   (fun uu____89307  ->
                      let uu____89308 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____89319  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____89308)
                  in
               match uu____89295 with
               | (r,ms) ->
                   ((let uu____89350 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____89350
                     then
                       let uu____89355 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____89357 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____89359 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____89355 uu____89357
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____89359
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
      fun uu____89397  ->
        match uu____89397 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____89440 =
                 let uu____89446 =
                   let uu____89448 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____89450 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____89448 uu____89450
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____89446)  in
               let uu____89454 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____89440 uu____89454)
               in
            let equiv1 v1 v' =
              let uu____89467 =
                let uu____89472 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____89473 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____89472, uu____89473)  in
              match uu____89467 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____89493 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____89524 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____89524 with
                      | FStar_Syntax_Syntax.U_unif uu____89531 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____89560  ->
                                    match uu____89560 with
                                    | (u,v') ->
                                        let uu____89569 = equiv1 v1 v'  in
                                        if uu____89569
                                        then
                                          let uu____89574 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____89574 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____89595 -> []))
               in
            let uu____89600 =
              let wl =
                let uu___4377_89604 = empty_worklist env  in
                {
                  attempting = (uu___4377_89604.attempting);
                  wl_deferred = (uu___4377_89604.wl_deferred);
                  ctr = (uu___4377_89604.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4377_89604.smt_ok);
                  umax_heuristic_ok = (uu___4377_89604.umax_heuristic_ok);
                  tcenv = (uu___4377_89604.tcenv);
                  wl_implicits = (uu___4377_89604.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____89623  ->
                      match uu____89623 with
                      | (lb,v1) ->
                          let uu____89630 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____89630 with
                           | USolved wl1 -> ()
                           | uu____89633 -> fail1 lb v1)))
               in
            let rec check_ineq uu____89644 =
              match uu____89644 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____89656) -> true
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
                      uu____89680,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____89682,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____89693) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____89701,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____89710 -> false)
               in
            let uu____89716 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____89733  ->
                      match uu____89733 with
                      | (u,v1) ->
                          let uu____89741 = check_ineq (u, v1)  in
                          if uu____89741
                          then true
                          else
                            ((let uu____89749 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____89749
                              then
                                let uu____89754 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____89756 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____89754
                                  uu____89756
                              else ());
                             false)))
               in
            if uu____89716
            then ()
            else
              ((let uu____89766 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____89766
                then
                  ((let uu____89772 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____89772);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____89784 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____89784))
                else ());
               (let uu____89797 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____89797))
  
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
        let fail1 uu____89871 =
          match uu____89871 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4454_89897 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___4454_89897.attempting);
            wl_deferred = (uu___4454_89897.wl_deferred);
            ctr = (uu___4454_89897.ctr);
            defer_ok;
            smt_ok = (uu___4454_89897.smt_ok);
            umax_heuristic_ok = (uu___4454_89897.umax_heuristic_ok);
            tcenv = (uu___4454_89897.tcenv);
            wl_implicits = (uu___4454_89897.wl_implicits)
          }  in
        (let uu____89900 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____89900
         then
           let uu____89905 = FStar_Util.string_of_bool defer_ok  in
           let uu____89907 = wl_to_string wl  in
           let uu____89909 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____89905 uu____89907 uu____89909
         else ());
        (let g1 =
           let uu____89915 = solve_and_commit env wl fail1  in
           match uu____89915 with
           | FStar_Pervasives_Native.Some
               (uu____89922::uu____89923,uu____89924) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4469_89953 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___4469_89953.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___4469_89953.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____89954 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___4474_89963 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4474_89963.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4474_89963.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___4474_89963.FStar_TypeChecker_Env.implicits)
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
    let uu____90006 = FStar_ST.op_Bang last_proof_ns  in
    match uu____90006 with
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
            let uu___4493_90131 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___4493_90131.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___4493_90131.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___4493_90131.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____90132 =
            let uu____90134 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____90134  in
          if uu____90132
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____90146 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____90147 =
                       let uu____90149 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____90149
                        in
                     FStar_Errors.diag uu____90146 uu____90147)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____90157 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____90158 =
                        let uu____90160 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____90160
                         in
                      FStar_Errors.diag uu____90157 uu____90158)
                   else ();
                   (let uu____90166 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____90166
                      "discharge_guard'" env vc1);
                   (let uu____90168 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____90168 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____90177 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____90178 =
                                let uu____90180 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____90180
                                 in
                              FStar_Errors.diag uu____90177 uu____90178)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____90190 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____90191 =
                                let uu____90193 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____90193
                                 in
                              FStar_Errors.diag uu____90190 uu____90191)
                           else ();
                           (let vcs =
                              let uu____90207 = FStar_Options.use_tactics ()
                                 in
                              if uu____90207
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____90229  ->
                                     (let uu____90231 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____90231);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____90275  ->
                                              match uu____90275 with
                                              | (env1,goal,opts) ->
                                                  let uu____90291 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____90291, opts)))))
                              else
                                (let uu____90294 =
                                   let uu____90301 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____90301)  in
                                 [uu____90294])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____90334  ->
                                    match uu____90334 with
                                    | (env1,goal,opts) ->
                                        let uu____90344 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____90344 with
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
                                                (let uu____90356 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____90357 =
                                                   let uu____90359 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____90361 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____90359 uu____90361
                                                    in
                                                 FStar_Errors.diag
                                                   uu____90356 uu____90357)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____90368 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____90369 =
                                                   let uu____90371 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____90371
                                                    in
                                                 FStar_Errors.diag
                                                   uu____90368 uu____90369)
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
      let uu____90389 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____90389 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____90398 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____90398
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____90412 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____90412 with
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
        let uu____90442 = try_teq false env t1 t2  in
        match uu____90442 with
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
            let uu____90486 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____90486 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____90499 ->
                     let uu____90512 =
                       let uu____90513 = FStar_Syntax_Subst.compress r  in
                       uu____90513.FStar_Syntax_Syntax.n  in
                     (match uu____90512 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____90518) ->
                          unresolved ctx_u'
                      | uu____90535 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____90559 = acc  in
            match uu____90559 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____90578 = hd1  in
                     (match uu____90578 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____90589 = unresolved ctx_u  in
                             if uu____90589
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____90613 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____90613
                                     then
                                       let uu____90617 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____90617
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____90626 = teq_nosmt env1 t tm
                                          in
                                       match uu____90626 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4606_90636 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4606_90636.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4606_90636.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4606_90636.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4606_90636.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4606_90636.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4606_90636.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4606_90636.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4609_90644 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4609_90644.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4609_90644.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4609_90644.FStar_TypeChecker_Env.imp_range)
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
                                    let uu___4613_90655 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4613_90655.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4613_90655.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4613_90655.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4613_90655.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4613_90655.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4613_90655.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4613_90655.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4613_90655.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4613_90655.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4613_90655.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4613_90655.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4613_90655.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4613_90655.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4613_90655.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4613_90655.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4613_90655.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4613_90655.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4613_90655.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4613_90655.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4613_90655.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4613_90655.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4613_90655.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4613_90655.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4613_90655.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4613_90655.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4613_90655.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4613_90655.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4613_90655.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4613_90655.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4613_90655.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4613_90655.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4613_90655.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4613_90655.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4613_90655.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4613_90655.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4613_90655.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4613_90655.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4613_90655.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4613_90655.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4613_90655.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4613_90655.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4613_90655.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4618_90659 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4618_90659.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4618_90659.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4618_90659.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4618_90659.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4618_90659.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4618_90659.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4618_90659.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4618_90659.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4618_90659.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4618_90659.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4618_90659.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4618_90659.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4618_90659.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4618_90659.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4618_90659.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4618_90659.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4618_90659.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4618_90659.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4618_90659.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4618_90659.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4618_90659.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4618_90659.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4618_90659.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4618_90659.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4618_90659.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4618_90659.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4618_90659.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4618_90659.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4618_90659.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4618_90659.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4618_90659.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4618_90659.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4618_90659.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4618_90659.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4618_90659.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4618_90659.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4618_90659.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4618_90659.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4618_90659.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4618_90659.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4618_90659.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4618_90659.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____90664 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____90664
                                   then
                                     let uu____90669 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____90671 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____90673 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____90675 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____90669 uu____90671 uu____90673
                                       reason uu____90675
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4624_90682  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____90689 =
                                             let uu____90699 =
                                               let uu____90707 =
                                                 let uu____90709 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____90711 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____90713 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____90709 uu____90711
                                                   uu____90713
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____90707, r)
                                                in
                                             [uu____90699]  in
                                           FStar_Errors.add_errors
                                             uu____90689);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4632_90733 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4632_90733.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4632_90733.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4632_90733.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____90737 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____90748  ->
                                               let uu____90749 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____90751 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____90753 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____90749 uu____90751
                                                 reason uu____90753)) env2 g2
                                         true
                                        in
                                     match uu____90737 with
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
          let uu___4640_90761 = g  in
          let uu____90762 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4640_90761.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4640_90761.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4640_90761.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____90762
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
        let uu____90805 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____90805 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____90806 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____90806
      | imp::uu____90808 ->
          let uu____90811 =
            let uu____90817 =
              let uu____90819 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____90821 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____90819 uu____90821 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____90817)
             in
          FStar_Errors.raise_error uu____90811
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90843 = teq_nosmt env t1 t2  in
        match uu____90843 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4662_90862 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4662_90862.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4662_90862.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4662_90862.FStar_TypeChecker_Env.implicits)
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
        (let uu____90898 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____90898
         then
           let uu____90903 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____90905 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____90903
             uu____90905
         else ());
        (let uu____90910 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____90910 with
         | (prob,x,wl) ->
             let g =
               let uu____90929 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____90940  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____90929  in
             ((let uu____90961 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____90961
               then
                 let uu____90966 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____90968 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____90970 =
                   let uu____90972 = FStar_Util.must g  in
                   guard_to_string env uu____90972  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____90966 uu____90968 uu____90970
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
        let uu____91009 = check_subtyping env t1 t2  in
        match uu____91009 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____91028 =
              let uu____91029 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____91029 g  in
            FStar_Pervasives_Native.Some uu____91028
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____91048 = check_subtyping env t1 t2  in
        match uu____91048 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____91067 =
              let uu____91068 =
                let uu____91069 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____91069]  in
              FStar_TypeChecker_Env.close_guard env uu____91068 g  in
            FStar_Pervasives_Native.Some uu____91067
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____91107 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____91107
         then
           let uu____91112 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____91114 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____91112
             uu____91114
         else ());
        (let uu____91119 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____91119 with
         | (prob,x,wl) ->
             let g =
               let uu____91134 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____91145  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____91134  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____91169 =
                      let uu____91170 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____91170]  in
                    FStar_TypeChecker_Env.close_guard env uu____91169 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____91211 = subtype_nosmt env t1 t2  in
        match uu____91211 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  