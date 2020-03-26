open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type lstring = Prims.string FStar_Thunk.t
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____49 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____84 -> false
  
let (__proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe))
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  umax_heuristic_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env ;
  wl_implicits: FStar_TypeChecker_Common.implicits }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
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
  worklist -> FStar_TypeChecker_Common.implicits) =
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
                    let uu____515 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____515;
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
                       FStar_TypeChecker_Common.imp_reason = reason;
                       FStar_TypeChecker_Common.imp_uvar = ctx_uvar;
                       FStar_TypeChecker_Common.imp_tm = t;
                       FStar_TypeChecker_Common.imp_range = r
                     }  in
                   (ctx_uvar, t,
                     (let uu___71_547 = wl  in
                      {
                        attempting = (uu___71_547.attempting);
                        wl_deferred = (uu___71_547.wl_deferred);
                        ctr = (uu___71_547.ctr);
                        defer_ok = (uu___71_547.defer_ok);
                        smt_ok = (uu___71_547.smt_ok);
                        umax_heuristic_ok = (uu___71_547.umax_heuristic_ok);
                        tcenv = (uu___71_547.tcenv);
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
            let uu___77_580 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___77_580.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___77_580.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___77_580.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___77_580.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___77_580.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___77_580.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___77_580.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___77_580.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___77_580.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___77_580.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___77_580.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___77_580.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___77_580.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___77_580.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___77_580.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___77_580.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___77_580.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___77_580.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___77_580.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___77_580.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___77_580.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___77_580.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___77_580.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___77_580.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___77_580.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___77_580.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___77_580.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___77_580.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___77_580.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___77_580.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___77_580.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___77_580.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___77_580.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___77_580.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___77_580.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___77_580.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___77_580.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___77_580.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___77_580.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___77_580.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___77_580.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___77_580.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___77_580.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___77_580.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___77_580.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___77_580.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____582 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____582 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
let (copy_uvar_for_type :
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
            let uu___85_624 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___85_624.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___85_624.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___85_624.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___85_624.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___85_624.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___85_624.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___85_624.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___85_624.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___85_624.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___85_624.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___85_624.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___85_624.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___85_624.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___85_624.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___85_624.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___85_624.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___85_624.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___85_624.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___85_624.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___85_624.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___85_624.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___85_624.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___85_624.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___85_624.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___85_624.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___85_624.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___85_624.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___85_624.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___85_624.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___85_624.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___85_624.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___85_624.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___85_624.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___85_624.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___85_624.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___85_624.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___85_624.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___85_624.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___85_624.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___85_624.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___85_624.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___85_624.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___85_624.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___85_624.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___85_624.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___85_624.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____626 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____626 t
            FStar_Syntax_Syntax.Allow_unresolved
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____687 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____722 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____752 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____763 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____774 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_792  ->
    match uu___0_792 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____804 = FStar_Syntax_Util.head_and_args t  in
    match uu____804 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____867 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____869 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____884 =
                     let uu____886 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____886  in
                   FStar_Util.format1 "@<%s>" uu____884
                in
             let uu____890 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____867 uu____869 uu____890
         | uu____893 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_905  ->
      match uu___1_905 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____910 =
            let uu____914 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____916 =
              let uu____920 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____922 =
                let uu____926 =
                  let uu____930 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____930]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____926
                 in
              uu____920 :: uu____922  in
            uu____914 :: uu____916  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____910
      | FStar_TypeChecker_Common.CProb p ->
          let uu____941 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____943 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____945 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____941 uu____943
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____945
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_959  ->
      match uu___2_959 with
      | UNIV (u,t) ->
          let x =
            let uu____965 = FStar_Options.hide_uvar_nums ()  in
            if uu____965
            then "?"
            else
              (let uu____972 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____972 FStar_Util.string_of_int)
             in
          let uu____976 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____976
      | TERM (u,t) ->
          let x =
            let uu____983 = FStar_Options.hide_uvar_nums ()  in
            if uu____983
            then "?"
            else
              (let uu____990 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____990 FStar_Util.string_of_int)
             in
          let uu____994 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____994
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1013 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1013 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1034 =
      let uu____1038 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1038
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1034 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1057 .
    (FStar_Syntax_Syntax.term * 'Auu____1057) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1076 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1097  ->
              match uu____1097 with
              | (x,uu____1104) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1076 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    {
      attempting = [];
      wl_deferred = [];
      ctr = Prims.int_zero;
      defer_ok = true;
      smt_ok = true;
      umax_heuristic_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    lstring -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1144 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1144
         then
           let uu____1149 = FStar_Thunk.force reason  in
           let uu____1152 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1149 uu____1152
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1175 = FStar_Thunk.mk (fun uu____1178  -> reason)  in
        giveup env uu____1175 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1184  ->
    match uu___3_1184 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1190 .
    'Auu____1190 FStar_TypeChecker_Common.problem ->
      'Auu____1190 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___149_1202 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___149_1202.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___149_1202.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___149_1202.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___149_1202.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___149_1202.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___149_1202.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___149_1202.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1210 .
    'Auu____1210 FStar_TypeChecker_Common.problem ->
      'Auu____1210 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1230  ->
    match uu___4_1230 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1236  -> FStar_TypeChecker_Common.TProb _1236)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1242  -> FStar_TypeChecker_Common.CProb _1242)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1248  ->
    match uu___5_1248 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___161_1254 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___161_1254.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___161_1254.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___161_1254.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___161_1254.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___161_1254.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___161_1254.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___161_1254.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___161_1254.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___161_1254.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___165_1262 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___165_1262.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___165_1262.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___165_1262.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___165_1262.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___165_1262.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___165_1262.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___165_1262.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___165_1262.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___165_1262.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1275  ->
      match uu___6_1275 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1282  ->
    match uu___7_1282 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1295  ->
    match uu___8_1295 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1310  ->
    match uu___9_1310 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1325  ->
    match uu___10_1325 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1339  ->
    match uu___11_1339 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1353  ->
    match uu___12_1353 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1365  ->
    match uu___13_1365 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1381 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1381) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1411 =
          let uu____1413 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1413  in
        if uu____1411
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1450)::bs ->
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
          let uu____1497 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1521 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1521]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1497
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1549 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1573 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1573]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1549
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1620 =
          let uu____1622 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1622  in
        if uu____1620
        then ()
        else
          (let uu____1627 =
             let uu____1630 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1630
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1627 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1679 =
          let uu____1681 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1681  in
        if uu____1679
        then ()
        else
          (let uu____1686 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1686)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1706 =
        let uu____1708 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1708  in
      if uu____1706
      then ()
      else
        (let msgf m =
           let uu____1722 =
             let uu____1724 =
               let uu____1726 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____1726 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____1724  in
           Prims.op_Hat msg uu____1722  in
         (let uu____1731 = msgf "scope"  in
          let uu____1734 = p_scope prob  in
          def_scope_wf uu____1731 (p_loc prob) uu____1734);
         (let uu____1746 = msgf "guard"  in
          def_check_scoped uu____1746 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1753 = msgf "lhs"  in
                def_check_scoped uu____1753 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1756 = msgf "rhs"  in
                def_check_scoped uu____1756 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1763 = msgf "lhs"  in
                def_check_scoped_comp uu____1763 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1766 = msgf "rhs"  in
                def_check_scoped_comp uu____1766 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___258_1787 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___258_1787.wl_deferred);
          ctr = (uu___258_1787.ctr);
          defer_ok = (uu___258_1787.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___258_1787.umax_heuristic_ok);
          tcenv = (uu___258_1787.tcenv);
          wl_implicits = (uu___258_1787.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1795 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1795 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___262_1818 = empty_worklist env  in
      let uu____1819 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1819;
        wl_deferred = (uu___262_1818.wl_deferred);
        ctr = (uu___262_1818.ctr);
        defer_ok = (uu___262_1818.defer_ok);
        smt_ok = (uu___262_1818.smt_ok);
        umax_heuristic_ok = (uu___262_1818.umax_heuristic_ok);
        tcenv = (uu___262_1818.tcenv);
        wl_implicits = (uu___262_1818.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___267_1840 = wl  in
        {
          attempting = (uu___267_1840.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___267_1840.ctr);
          defer_ok = (uu___267_1840.defer_ok);
          smt_ok = (uu___267_1840.smt_ok);
          umax_heuristic_ok = (uu___267_1840.umax_heuristic_ok);
          tcenv = (uu___267_1840.tcenv);
          wl_implicits = (uu___267_1840.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____1867 = FStar_Thunk.mkv reason  in defer uu____1867 prob wl
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___275_1886 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___275_1886.wl_deferred);
         ctr = (uu___275_1886.ctr);
         defer_ok = (uu___275_1886.defer_ok);
         smt_ok = (uu___275_1886.smt_ok);
         umax_heuristic_ok = (uu___275_1886.umax_heuristic_ok);
         tcenv = (uu___275_1886.tcenv);
         wl_implicits = (uu___275_1886.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1900 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1900 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____1934 = FStar_Syntax_Util.type_u ()  in
            match uu____1934 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____1946 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____1946 with
                 | (uu____1964,tt,wl1) ->
                     let uu____1967 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____1967, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_1973  ->
    match uu___14_1973 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _1979  -> FStar_TypeChecker_Common.TProb _1979) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _1985  -> FStar_TypeChecker_Common.CProb _1985) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1993 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1993 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2013  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2055 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2055 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2055 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2055 FStar_TypeChecker_Common.problem *
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
                        let uu____2142 =
                          let uu____2151 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2151]  in
                        FStar_List.append scope uu____2142
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2194 =
                      let uu____2197 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2197  in
                    FStar_List.append uu____2194
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2216 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2216 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2242 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2242;
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
                  (let uu____2316 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2316 with
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
                  (let uu____2404 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2404 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2442 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2442 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2442 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2442 FStar_TypeChecker_Common.problem *
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
                          let uu____2510 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2510]  in
                        let uu____2529 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2529
                     in
                  let uu____2532 =
                    let uu____2539 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___358_2550 = wl  in
                       {
                         attempting = (uu___358_2550.attempting);
                         wl_deferred = (uu___358_2550.wl_deferred);
                         ctr = (uu___358_2550.ctr);
                         defer_ok = (uu___358_2550.defer_ok);
                         smt_ok = (uu___358_2550.smt_ok);
                         umax_heuristic_ok =
                           (uu___358_2550.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___358_2550.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2539
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2532 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2568 =
                              let uu____2573 =
                                let uu____2574 =
                                  let uu____2583 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2583
                                   in
                                [uu____2574]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2573  in
                            uu____2568 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2611 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2611;
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
                let uu____2659 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2659;
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
  'Auu____2674 .
    worklist ->
      'Auu____2674 FStar_TypeChecker_Common.problem ->
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
              let uu____2707 =
                let uu____2710 =
                  let uu____2711 =
                    let uu____2718 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2718)  in
                  FStar_Syntax_Syntax.NT uu____2711  in
                [uu____2710]  in
              FStar_Syntax_Subst.subst uu____2707 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2740 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2740
        then
          let uu____2748 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2751 = prob_to_string env d  in
          let uu____2753 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____2760 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2748 uu____2751 uu____2753 uu____2760
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2772 -> failwith "impossible"  in
           let uu____2775 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 FStar_TypeChecker_Err.print_discrepancy
                   (FStar_TypeChecker_Normalize.term_to_string env)
                   tp.FStar_TypeChecker_Common.lhs
                   tp.FStar_TypeChecker_Common.rhs
             | FStar_TypeChecker_Common.CProb cp ->
                 FStar_TypeChecker_Err.print_discrepancy
                   (FStar_TypeChecker_Normalize.comp_to_string env)
                   cp.FStar_TypeChecker_Common.lhs
                   cp.FStar_TypeChecker_Common.rhs
              in
           match uu____2775 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2818  ->
            match uu___15_2818 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2830 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2834 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2834 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2865  ->
           match uu___16_2865 with
           | UNIV uu____2868 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2875 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2875
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
        (fun uu___17_2903  ->
           match uu___17_2903 with
           | UNIV (u',t) ->
               let uu____2908 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2908
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2915 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2927 =
        let uu____2928 =
          let uu____2929 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2929
           in
        FStar_Syntax_Subst.compress uu____2928  in
      FStar_All.pipe_right uu____2927 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2941 =
        let uu____2942 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____2942  in
      FStar_All.pipe_right uu____2941 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2954 =
        let uu____2958 =
          let uu____2960 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____2960  in
        FStar_Pervasives_Native.Some uu____2958  in
      FStar_Profiling.profile (fun uu____2963  -> sn' env t) uu____2954
        "FStar.TypeChecker.Rel.sn"
  
let (norm_with_steps :
  Prims.string ->
    FStar_TypeChecker_Env.steps ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun profiling_tag  ->
    fun steps  ->
      fun env  ->
        fun t  ->
          let uu____2988 =
            let uu____2992 =
              let uu____2994 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____2994  in
            FStar_Pervasives_Native.Some uu____2992  in
          FStar_Profiling.profile
            (fun uu____2997  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____2988
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3005 = FStar_Syntax_Util.head_and_args t  in
    match uu____3005 with
    | (h,uu____3024) ->
        let uu____3049 =
          let uu____3050 = FStar_Syntax_Subst.compress h  in
          uu____3050.FStar_Syntax_Syntax.n  in
        (match uu____3049 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3055 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3068 =
        let uu____3072 =
          let uu____3074 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3074  in
        FStar_Pervasives_Native.Some uu____3072  in
      FStar_Profiling.profile
        (fun uu____3079  ->
           let uu____3080 = should_strongly_reduce t  in
           if uu____3080
           then
             let uu____3083 =
               let uu____3084 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3084  in
             FStar_All.pipe_right uu____3083 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3068 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'Auu____3095 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3095) ->
        (FStar_Syntax_Syntax.term * 'Auu____3095)
  =
  fun env  ->
    fun t  ->
      let uu____3118 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3118, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3170  ->
              match uu____3170 with
              | (x,imp) ->
                  let uu____3189 =
                    let uu___464_3190 = x  in
                    let uu____3191 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___464_3190.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___464_3190.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3191
                    }  in
                  (uu____3189, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3215 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3215
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3219 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3219
        | uu____3222 -> u2  in
      let uu____3223 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3223
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3240 =
          let uu____3244 =
            let uu____3246 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3246  in
          FStar_Pervasives_Native.Some uu____3244  in
        FStar_Profiling.profile
          (fun uu____3249  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3240 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
          normalize_refinement steps env1 t  in
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____3371 = norm_refinement env t12  in
                 match uu____3371 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3386;
                     FStar_Syntax_Syntax.vars = uu____3387;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3411 =
                       let uu____3413 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3415 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3413 uu____3415
                        in
                     failwith uu____3411)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3431 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3431
          | FStar_Syntax_Syntax.Tm_uinst uu____3432 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3469 =
                   let uu____3470 = FStar_Syntax_Subst.compress t1'  in
                   uu____3470.FStar_Syntax_Syntax.n  in
                 match uu____3469 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3485 -> aux true t1'
                 | uu____3493 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3508 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3539 =
                   let uu____3540 = FStar_Syntax_Subst.compress t1'  in
                   uu____3540.FStar_Syntax_Syntax.n  in
                 match uu____3539 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3555 -> aux true t1'
                 | uu____3563 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3578 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3625 =
                   let uu____3626 = FStar_Syntax_Subst.compress t1'  in
                   uu____3626.FStar_Syntax_Syntax.n  in
                 match uu____3625 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3641 -> aux true t1'
                 | uu____3649 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3664 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3679 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3694 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3709 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3724 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3753 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3786 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3807 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3834 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3862 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3899 ->
              let uu____3906 =
                let uu____3908 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3910 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3908 uu____3910
                 in
              failwith uu____3906
          | FStar_Syntax_Syntax.Tm_ascribed uu____3925 ->
              let uu____3952 =
                let uu____3954 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3956 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3954 uu____3956
                 in
              failwith uu____3952
          | FStar_Syntax_Syntax.Tm_delayed uu____3971 ->
              let uu____3994 =
                let uu____3996 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3998 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3996 uu____3998
                 in
              failwith uu____3994
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4013 =
                let uu____4015 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4017 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4015 uu____4017
                 in
              failwith uu____4013
           in
        let uu____4032 = whnf env t1  in aux false uu____4032
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun t  ->
      let uu____4077 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4077 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4118 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4118, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4145 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4145 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4205  ->
    match uu____4205 with
    | (t_base,refopt) ->
        let uu____4236 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4236 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4278 =
      let uu____4282 =
        let uu____4285 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4310  ->
                  match uu____4310 with | (uu____4318,uu____4319,x) -> x))
           in
        FStar_List.append wl.attempting uu____4285  in
      FStar_List.map (wl_prob_to_string wl) uu____4282  in
    FStar_All.pipe_right uu____4278 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____4340 .
    ('Auu____4340 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4352  ->
    match uu____4352 with
    | (uu____4359,c,args) ->
        let uu____4362 = print_ctx_uvar c  in
        let uu____4364 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4362 uu____4364
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4374 = FStar_Syntax_Util.head_and_args t  in
    match uu____4374 with
    | (head1,_args) ->
        let uu____4418 =
          let uu____4419 = FStar_Syntax_Subst.compress head1  in
          uu____4419.FStar_Syntax_Syntax.n  in
        (match uu____4418 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4423 -> true
         | uu____4437 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4445 = FStar_Syntax_Util.head_and_args t  in
    match uu____4445 with
    | (head1,_args) ->
        let uu____4488 =
          let uu____4489 = FStar_Syntax_Subst.compress head1  in
          uu____4489.FStar_Syntax_Syntax.n  in
        (match uu____4488 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4493) -> u
         | uu____4510 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4535 = FStar_Syntax_Util.head_and_args t  in
      match uu____4535 with
      | (head1,args) ->
          let uu____4582 =
            let uu____4583 = FStar_Syntax_Subst.compress head1  in
            uu____4583.FStar_Syntax_Syntax.n  in
          (match uu____4582 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4591)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4624 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_4649  ->
                         match uu___18_4649 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4654 =
                               let uu____4655 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4655.FStar_Syntax_Syntax.n  in
                             (match uu____4654 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4660 -> false)
                         | uu____4662 -> true))
                  in
               (match uu____4624 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4687 =
                        FStar_List.collect
                          (fun uu___19_4699  ->
                             match uu___19_4699 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4703 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4703]
                             | uu____4704 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4687 FStar_List.rev  in
                    let uu____4727 =
                      let uu____4734 =
                        let uu____4743 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_4765  ->
                                  match uu___20_4765 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4769 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4769]
                                  | uu____4770 -> []))
                           in
                        FStar_All.pipe_right uu____4743 FStar_List.rev  in
                      let uu____4793 =
                        let uu____4796 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4796  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4734 uu____4793
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____4727 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4832  ->
                                match uu____4832 with
                                | (x,i) ->
                                    let uu____4851 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4851, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4882  ->
                                match uu____4882 with
                                | (a,i) ->
                                    let uu____4901 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4901, i)) args_sol
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
           | uu____4923 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4945 =
          let uu____4968 =
            let uu____4969 = FStar_Syntax_Subst.compress k  in
            uu____4969.FStar_Syntax_Syntax.n  in
          match uu____4968 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5051 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5051)
              else
                (let uu____5086 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5086 with
                 | (ys',t1,uu____5119) ->
                     let uu____5124 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5124))
          | uu____5163 ->
              let uu____5164 =
                let uu____5169 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5169)  in
              ((ys, t), uu____5164)
           in
        match uu____4945 with
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
                 let uu____5264 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5264 c  in
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
               (let uu____5342 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5342
                then
                  let uu____5347 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5349 = print_ctx_uvar uv  in
                  let uu____5351 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5347 uu____5349 uu____5351
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5360 =
                   let uu____5362 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5362  in
                 let uu____5365 =
                   let uu____5368 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5368
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5360 uu____5365 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5401 =
               let uu____5402 =
                 let uu____5404 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5406 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5404 uu____5406
                  in
               failwith uu____5402  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5472  ->
                       match uu____5472 with
                       | (a,i) ->
                           let uu____5493 =
                             let uu____5494 = FStar_Syntax_Subst.compress a
                                in
                             uu____5494.FStar_Syntax_Syntax.n  in
                           (match uu____5493 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5520 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5530 =
                 let uu____5532 = is_flex g  in Prims.op_Negation uu____5532
                  in
               if uu____5530
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5541 = destruct_flex_t g wl  in
                  match uu____5541 with
                  | ((uu____5546,uv1,args),wl1) ->
                      ((let uu____5551 = args_as_binders args  in
                        assign_solution uu____5551 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___717_5553 = wl1  in
              {
                attempting = (uu___717_5553.attempting);
                wl_deferred = (uu___717_5553.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___717_5553.defer_ok);
                smt_ok = (uu___717_5553.smt_ok);
                umax_heuristic_ok = (uu___717_5553.umax_heuristic_ok);
                tcenv = (uu___717_5553.tcenv);
                wl_implicits = (uu___717_5553.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5578 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5578
         then
           let uu____5583 = FStar_Util.string_of_int pid  in
           let uu____5585 =
             let uu____5587 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5587 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5583 uu____5585
         else ());
        commit sol;
        (let uu___725_5601 = wl  in
         {
           attempting = (uu___725_5601.attempting);
           wl_deferred = (uu___725_5601.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___725_5601.defer_ok);
           smt_ok = (uu___725_5601.smt_ok);
           umax_heuristic_ok = (uu___725_5601.umax_heuristic_ok);
           tcenv = (uu___725_5601.tcenv);
           wl_implicits = (uu___725_5601.wl_implicits)
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
          (let uu____5637 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____5637
           then
             let uu____5642 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____5646 =
               let uu____5648 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____5648 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5642 uu____5646
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____5683 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5683 FStar_Util.set_elements  in
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
      let uu____5723 = occurs uk t  in
      match uu____5723 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5762 =
                 let uu____5764 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5766 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5764 uu____5766
                  in
               FStar_Pervasives_Native.Some uu____5762)
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
            let uu____5886 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5886 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5937 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5994  ->
             match uu____5994 with
             | (x,uu____6006) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6024 = FStar_List.last bs  in
      match uu____6024 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6048) ->
          let uu____6059 =
            FStar_Util.prefix_until
              (fun uu___21_6074  ->
                 match uu___21_6074 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6077 -> false) g
             in
          (match uu____6059 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6091,bx,rest) -> bx :: rest)
  
let (tgt_ctx_includes_src_ctx :
  FStar_Syntax_Syntax.ctx_uvar -> FStar_Syntax_Syntax.ctx_uvar -> Prims.bool)
  =
  fun tgt  ->
    fun src  ->
      let uu____6124 =
        maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
          src.FStar_Syntax_Syntax.ctx_uvar_binders
         in
      match uu____6124 with
      | (pfx,uu____6135) ->
          (FStar_List.length pfx) =
            (FStar_List.length src.FStar_Syntax_Syntax.ctx_uvar_binders)
  
let (tgt_ctx_includes_all_source_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar Prims.list -> Prims.bool)
  =
  fun tgt  ->
    fun sources  -> FStar_List.for_all (tgt_ctx_includes_src_ctx tgt) sources
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6188 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6188 with
        | (pfx,uu____6198) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6210 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6210 with
             | (uu____6218,src',wl1) ->
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
                 | uu____6332 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6333 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6397  ->
                  fun uu____6398  ->
                    match (uu____6397, uu____6398) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6501 =
                          let uu____6503 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6503
                           in
                        if uu____6501
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6537 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6537
                           then
                             let uu____6554 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6554)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6333 with | (isect,uu____6604) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6640 'Auu____6641 .
    (FStar_Syntax_Syntax.bv * 'Auu____6640) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6641) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6699  ->
              fun uu____6700  ->
                match (uu____6699, uu____6700) with
                | ((a,uu____6719),(b,uu____6721)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6737 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6737) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6768  ->
           match uu____6768 with
           | (y,uu____6775) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6785 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6785) Prims.list ->
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
                   let uu____6947 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6947
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6980 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7032 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7076 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7097 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7105  ->
    match uu___22_7105 with
    | MisMatch (d1,d2) ->
        let uu____7117 =
          let uu____7119 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7121 =
            let uu____7123 =
              let uu____7125 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7125 ")"  in
            Prims.op_Hat ") (" uu____7123  in
          Prims.op_Hat uu____7119 uu____7121  in
        Prims.op_Hat "MisMatch (" uu____7117
    | HeadMatch u ->
        let uu____7132 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7132
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7141  ->
    match uu___23_7141 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7158 -> HeadMatch false
  
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
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7180 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7180 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7191 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7215 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7225 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7252 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7252
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7253 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7254 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7255 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7268 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7282 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7306) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7312,uu____7313) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7355) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7380;
             FStar_Syntax_Syntax.index = uu____7381;
             FStar_Syntax_Syntax.sort = t2;_},uu____7383)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7391 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7392 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7393 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7408 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7415 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7435 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7435
  
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
           { FStar_Syntax_Syntax.blob = uu____7454;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7455;
             FStar_Syntax_Syntax.ltyp = uu____7456;
             FStar_Syntax_Syntax.rng = uu____7457;_},uu____7458)
            ->
            let uu____7469 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7469 t21
        | (uu____7470,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7471;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7472;
             FStar_Syntax_Syntax.ltyp = uu____7473;
             FStar_Syntax_Syntax.rng = uu____7474;_})
            ->
            let uu____7485 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7485
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7497 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7497
            then FullMatch
            else
              (let uu____7502 =
                 let uu____7511 =
                   let uu____7514 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7514  in
                 let uu____7515 =
                   let uu____7518 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7518  in
                 (uu____7511, uu____7515)  in
               MisMatch uu____7502)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7524),FStar_Syntax_Syntax.Tm_uinst (g,uu____7526)) ->
            let uu____7535 = head_matches env f g  in
            FStar_All.pipe_right uu____7535 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7536) -> HeadMatch true
        | (uu____7538,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7542 = FStar_Const.eq_const c d  in
            if uu____7542
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7552),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7554)) ->
            let uu____7587 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7587
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7597),FStar_Syntax_Syntax.Tm_refine (y,uu____7599)) ->
            let uu____7608 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7608 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7610),uu____7611) ->
            let uu____7616 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7616 head_match
        | (uu____7617,FStar_Syntax_Syntax.Tm_refine (x,uu____7619)) ->
            let uu____7624 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7624 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7625,FStar_Syntax_Syntax.Tm_type
           uu____7626) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7628,FStar_Syntax_Syntax.Tm_arrow uu____7629) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7660),FStar_Syntax_Syntax.Tm_app (head',uu____7662))
            ->
            let uu____7711 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7711 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7713),uu____7714) ->
            let uu____7739 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7739 head_match
        | (uu____7740,FStar_Syntax_Syntax.Tm_app (head1,uu____7742)) ->
            let uu____7767 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7767 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7768,FStar_Syntax_Syntax.Tm_let
           uu____7769) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7797,FStar_Syntax_Syntax.Tm_match uu____7798) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7844,FStar_Syntax_Syntax.Tm_abs
           uu____7845) -> HeadMatch true
        | uu____7883 ->
            let uu____7888 =
              let uu____7897 = delta_depth_of_term env t11  in
              let uu____7900 = delta_depth_of_term env t21  in
              (uu____7897, uu____7900)  in
            MisMatch uu____7888
  
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
              let uu____7969 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7969  in
            (let uu____7971 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7971
             then
               let uu____7976 = FStar_Syntax_Print.term_to_string t  in
               let uu____7978 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7976 uu____7978
             else ());
            (let uu____7983 =
               let uu____7984 = FStar_Syntax_Util.un_uinst head1  in
               uu____7984.FStar_Syntax_Syntax.n  in
             match uu____7983 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7990 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7990 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8004 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____8004
                        then
                          let uu____8009 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8009
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8014 ->
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
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.1" steps env
                          t
                         in
                      let uu____8032 =
                        let uu____8034 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8034 = FStar_Syntax_Util.Equal  in
                      if uu____8032
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8041 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8041
                          then
                            let uu____8046 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8048 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8046
                              uu____8048
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8053 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail1 d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let rec aux retry1 n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            (let uu____8205 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8205
             then
               let uu____8210 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8212 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8214 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8210
                 uu____8212 uu____8214
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8242 =
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
               match uu____8242 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8290 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8290 with
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
                   aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             match r with
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  i),FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level j))
                 when
                 ((i > Prims.int_zero) || (j > Prims.int_zero)) && (i <> j)
                 ->
                 reduce_one_and_try_again
                   (FStar_Syntax_Syntax.Delta_equational_at_level i)
                   (FStar_Syntax_Syntax.Delta_equational_at_level j)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____8328),uu____8329)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8350 =
                      let uu____8359 = maybe_inline t11  in
                      let uu____8362 = maybe_inline t21  in
                      (uu____8359, uu____8362)  in
                    match uu____8350 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (uu____8405,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8406))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8427 =
                      let uu____8436 = maybe_inline t11  in
                      let uu____8439 = maybe_inline t21  in
                      (uu____8436, uu____8439)  in
                    match uu____8427 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 when d1 = d2 -> reduce_both_and_try_again d1 r
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 -> reduce_one_and_try_again d1 d2
             | MisMatch uu____8494 -> fail1 n_delta r t11 t21
             | uu____8503 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8518 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8518
           then
             let uu____8523 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8525 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8527 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8535 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8552 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8552
                    (fun uu____8587  ->
                       match uu____8587 with
                       | (t11,t21) ->
                           let uu____8595 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8597 =
                             let uu____8599 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8599  in
                           Prims.op_Hat uu____8595 uu____8597))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8523 uu____8525 uu____8527 uu____8535
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8616 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8616 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8631  ->
    match uu___24_8631 with
    | FStar_TypeChecker_Common.Rigid_rigid  -> Prims.int_zero
    | FStar_TypeChecker_Common.Flex_rigid_eq  -> Prims.int_one
    | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> (Prims.of_int (2))
    | FStar_TypeChecker_Common.Flex_rigid  -> (Prims.of_int (3))
    | FStar_TypeChecker_Common.Rigid_flex  -> (Prims.of_int (4))
    | FStar_TypeChecker_Common.Flex_flex  -> (Prims.of_int (5))
  
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
      let uu___1221_8680 = p  in
      let uu____8683 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8684 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1221_8680.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8683;
        FStar_TypeChecker_Common.relation =
          (uu___1221_8680.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8684;
        FStar_TypeChecker_Common.element =
          (uu___1221_8680.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1221_8680.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1221_8680.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1221_8680.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1221_8680.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1221_8680.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8699 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8699
            (fun _8704  -> FStar_TypeChecker_Common.TProb _8704)
      | FStar_TypeChecker_Common.CProb uu____8705 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8728 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8728 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8736 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8736 with
           | (lh,lhs_args) ->
               let uu____8783 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8783 with
                | (rh,rhs_args) ->
                    let uu____8830 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8843,FStar_Syntax_Syntax.Tm_uvar uu____8844)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8933 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8960,uu____8961)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8976,FStar_Syntax_Syntax.Tm_uvar uu____8977)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8992,FStar_Syntax_Syntax.Tm_arrow uu____8993)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1272_9023 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1272_9023.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1272_9023.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1272_9023.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1272_9023.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1272_9023.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1272_9023.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1272_9023.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1272_9023.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1272_9023.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9026,FStar_Syntax_Syntax.Tm_type uu____9027)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1272_9043 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1272_9043.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1272_9043.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1272_9043.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1272_9043.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1272_9043.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1272_9043.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1272_9043.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1272_9043.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1272_9043.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9046,FStar_Syntax_Syntax.Tm_uvar uu____9047)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1272_9063 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1272_9063.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1272_9063.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1272_9063.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1272_9063.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1272_9063.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1272_9063.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1272_9063.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1272_9063.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1272_9063.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9066,FStar_Syntax_Syntax.Tm_uvar uu____9067)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9082,uu____9083)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9098,FStar_Syntax_Syntax.Tm_uvar uu____9099)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9114,uu____9115) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8830 with
                     | (rank,tp1) ->
                         let uu____9128 =
                           FStar_All.pipe_right
                             (let uu___1292_9132 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1292_9132.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1292_9132.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1292_9132.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1292_9132.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1292_9132.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1292_9132.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1292_9132.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1292_9132.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1292_9132.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9135  ->
                                FStar_TypeChecker_Common.TProb _9135)
                            in
                         (rank, uu____9128))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9139 =
            FStar_All.pipe_right
              (let uu___1296_9143 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1296_9143.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1296_9143.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1296_9143.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1296_9143.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1296_9143.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1296_9143.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1296_9143.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1296_9143.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1296_9143.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9146  -> FStar_TypeChecker_Common.CProb _9146)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9139)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9206 probs =
      match uu____9206 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9287 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9308 = rank wl.tcenv hd1  in
               (match uu____9308 with
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
                      (let uu____9369 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9374 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9374)
                          in
                       if uu____9369
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
          let uu____9447 = FStar_Syntax_Util.head_and_args t  in
          match uu____9447 with
          | (hd1,uu____9466) ->
              let uu____9491 =
                let uu____9492 = FStar_Syntax_Subst.compress hd1  in
                uu____9492.FStar_Syntax_Syntax.n  in
              (match uu____9491 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9497) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9532  ->
                           match uu____9532 with
                           | (y,uu____9541) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9564  ->
                                       match uu____9564 with
                                       | (x,uu____9573) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9578 -> false)
           in
        let uu____9580 = rank tcenv p  in
        match uu____9580 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9589 -> true
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
  | UFailed of lstring 
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____9644 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9663 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9682 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9699 = FStar_Thunk.mkv s  in UFailed uu____9699 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9714 = FStar_Thunk.mk s  in UFailed uu____9714 
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
                        let uu____9766 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9766 with
                        | (k,uu____9774) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9787 -> false)))
            | uu____9789 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9841 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9849 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9849 = Prims.int_zero))
                           in
                        if uu____9841 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9870 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9878 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9878 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9870)
               in
            let uu____9882 = filter1 u12  in
            let uu____9885 = filter1 u22  in (uu____9882, uu____9885)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9920 = filter_out_common_univs us1 us2  in
                   (match uu____9920 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9980 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9980 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9983 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10000  ->
                               let uu____10001 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10003 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10001 uu____10003))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10029 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10029 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10055 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10055 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10058 ->
                   ufailed_thunk
                     (fun uu____10069  ->
                        let uu____10070 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10072 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10070 uu____10072 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10075,uu____10076) ->
              let uu____10078 =
                let uu____10080 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10082 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10080 uu____10082
                 in
              failwith uu____10078
          | (FStar_Syntax_Syntax.U_unknown ,uu____10085) ->
              let uu____10086 =
                let uu____10088 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10090 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10088 uu____10090
                 in
              failwith uu____10086
          | (uu____10093,FStar_Syntax_Syntax.U_bvar uu____10094) ->
              let uu____10096 =
                let uu____10098 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10100 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10098 uu____10100
                 in
              failwith uu____10096
          | (uu____10103,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10104 =
                let uu____10106 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10108 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10106 uu____10108
                 in
              failwith uu____10104
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10138 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10138
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10155 = occurs_univ v1 u3  in
              if uu____10155
              then
                let uu____10158 =
                  let uu____10160 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10162 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10160 uu____10162
                   in
                try_umax_components u11 u21 uu____10158
              else
                (let uu____10167 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10167)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10179 = occurs_univ v1 u3  in
              if uu____10179
              then
                let uu____10182 =
                  let uu____10184 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10186 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10184 uu____10186
                   in
                try_umax_components u11 u21 uu____10182
              else
                (let uu____10191 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10191)
          | (FStar_Syntax_Syntax.U_max uu____10192,uu____10193) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10201 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10201
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10207,FStar_Syntax_Syntax.U_max uu____10208) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10216 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10216
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10222,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10224,FStar_Syntax_Syntax.U_name uu____10225) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10227) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10229) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10231,FStar_Syntax_Syntax.U_succ uu____10232) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10234,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
  
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
      let uu____10341 = bc1  in
      match uu____10341 with
      | (bs1,mk_cod1) ->
          let uu____10385 = bc2  in
          (match uu____10385 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10496 = aux xs ys  in
                     (match uu____10496 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10579 =
                       let uu____10586 = mk_cod1 xs  in ([], uu____10586)  in
                     let uu____10589 =
                       let uu____10596 = mk_cod2 ys  in ([], uu____10596)  in
                     (uu____10579, uu____10589)
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
                  let uu____10665 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10665 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10668 =
                    let uu____10669 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10669 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10668
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10674 = has_type_guard t1 t2  in (uu____10674, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10675 = has_type_guard t2 t1  in (uu____10675, wl)
  
let is_flex_pat :
  'Auu____10685 'Auu____10686 'Auu____10687 .
    ('Auu____10685 * 'Auu____10686 * 'Auu____10687 Prims.list) -> Prims.bool
  =
  fun uu___25_10701  ->
    match uu___25_10701 with
    | (uu____10710,uu____10711,[]) -> true
    | uu____10715 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10748 = f  in
      match uu____10748 with
      | (uu____10755,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10756;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10757;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10760;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10761;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10762;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10763;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10833  ->
                 match uu____10833 with
                 | (y,uu____10842) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10996 =
                  let uu____11011 =
                    let uu____11014 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11014  in
                  ((FStar_List.rev pat_binders), uu____11011)  in
                FStar_Pervasives_Native.Some uu____10996
            | (uu____11047,[]) ->
                let uu____11078 =
                  let uu____11093 =
                    let uu____11096 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11096  in
                  ((FStar_List.rev pat_binders), uu____11093)  in
                FStar_Pervasives_Native.Some uu____11078
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11187 =
                  let uu____11188 = FStar_Syntax_Subst.compress a  in
                  uu____11188.FStar_Syntax_Syntax.n  in
                (match uu____11187 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11208 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11208
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1624_11238 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1624_11238.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1624_11238.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11242 =
                            let uu____11243 =
                              let uu____11250 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11250)  in
                            FStar_Syntax_Syntax.NT uu____11243  in
                          [uu____11242]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1630_11266 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1630_11266.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1630_11266.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11267 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11307 =
                  let uu____11322 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11322  in
                (match uu____11307 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11397 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11430 ->
               let uu____11431 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11431 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11751 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11751
       then
         let uu____11756 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11756
       else ());
      (let uu____11761 = next_prob probs  in
       match uu____11761 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1655_11788 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1655_11788.wl_deferred);
               ctr = (uu___1655_11788.ctr);
               defer_ok = (uu___1655_11788.defer_ok);
               smt_ok = (uu___1655_11788.smt_ok);
               umax_heuristic_ok = (uu___1655_11788.umax_heuristic_ok);
               tcenv = (uu___1655_11788.tcenv);
               wl_implicits = (uu___1655_11788.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11797 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11797
                 then
                   let uu____11800 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11800
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
                       (let uu____11807 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd1
                            probs1
                           in
                        solve env uu____11807)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1667_11813 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1667_11813.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1667_11813.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1667_11813.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1667_11813.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1667_11813.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1667_11813.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1667_11813.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1667_11813.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1667_11813.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11838 ->
                let uu____11848 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11913  ->
                          match uu____11913 with
                          | (c,uu____11923,uu____11924) -> c < probs.ctr))
                   in
                (match uu____11848 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11972 =
                            let uu____11977 =
                              FStar_List.map
                                (fun uu____11998  ->
                                   match uu____11998 with
                                   | (uu____12014,x,y) ->
                                       let uu____12025 = FStar_Thunk.force x
                                          in
                                       (uu____12025, y)) probs.wl_deferred
                               in
                            (uu____11977, (probs.wl_implicits))  in
                          Success uu____11972
                      | uu____12029 ->
                          let uu____12039 =
                            let uu___1685_12040 = probs  in
                            let uu____12041 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12062  ->
                                      match uu____12062 with
                                      | (uu____12070,uu____12071,y) -> y))
                               in
                            {
                              attempting = uu____12041;
                              wl_deferred = rest;
                              ctr = (uu___1685_12040.ctr);
                              defer_ok = (uu___1685_12040.defer_ok);
                              smt_ok = (uu___1685_12040.smt_ok);
                              umax_heuristic_ok =
                                (uu___1685_12040.umax_heuristic_ok);
                              tcenv = (uu___1685_12040.tcenv);
                              wl_implicits = (uu___1685_12040.wl_implicits)
                            }  in
                          solve env uu____12039))))

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
            let uu____12080 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12080 with
            | USolved wl1 ->
                let uu____12082 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12082
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12085 = defer_lit "" orig wl1  in
                solve env uu____12085

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
                  let uu____12136 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12136 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12139 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12152;
                  FStar_Syntax_Syntax.vars = uu____12153;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12156;
                  FStar_Syntax_Syntax.vars = uu____12157;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12170,uu____12171) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12179,FStar_Syntax_Syntax.Tm_uinst uu____12180) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12188 -> USolved wl

and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> lstring -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____12199 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12199
              then
                let uu____12204 = prob_to_string env orig  in
                let uu____12206 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12204 uu____12206
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
               let uu____12299 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12299 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12354 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12354
                then
                  let uu____12359 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12361 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12359 uu____12361
                else ());
               (let uu____12366 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12366 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12412 = eq_prob t1 t2 wl2  in
                         (match uu____12412 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12433 ->
                         let uu____12442 = eq_prob t1 t2 wl2  in
                         (match uu____12442 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12492 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12507 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12508 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12507, uu____12508)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12513 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12514 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12513, uu____12514)
                            in
                         (match uu____12492 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12545 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12545 with
                                | (t1_hd,t1_args) ->
                                    let uu____12590 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12590 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12656 =
                                              let uu____12663 =
                                                let uu____12674 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12674 :: t1_args  in
                                              let uu____12691 =
                                                let uu____12700 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12700 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12749  ->
                                                   fun uu____12750  ->
                                                     fun uu____12751  ->
                                                       match (uu____12749,
                                                               uu____12750,
                                                               uu____12751)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12801),
                                                          (a2,uu____12803))
                                                           ->
                                                           let uu____12840 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12840
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12663
                                                uu____12691
                                               in
                                            match uu____12656 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1839_12866 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1839_12866.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1839_12866.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1839_12866.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12877 =
                                                  solve env1 wl'  in
                                                (match uu____12877 with
                                                 | Success (uu____12880,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1848_12884
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1848_12884.attempting);
                                                            wl_deferred =
                                                              (uu___1848_12884.wl_deferred);
                                                            ctr =
                                                              (uu___1848_12884.ctr);
                                                            defer_ok =
                                                              (uu___1848_12884.defer_ok);
                                                            smt_ok =
                                                              (uu___1848_12884.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1848_12884.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1848_12884.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12885 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12917 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12917 with
                                | (t1_base,p1_opt) ->
                                    let uu____12953 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12953 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____13052 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13052
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
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi11 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi1
                                                  in
                                               let phi21 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi2
                                                  in
                                               let uu____13105 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13105
                                           | (FStar_Pervasives_Native.None
                                              ,FStar_Pervasives_Native.Some
                                              (x,phi)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____13137 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13137
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi),FStar_Pervasives_Native.None
                                              ) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____13169 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13169
                                           | uu____13172 -> t_base  in
                                         let uu____13189 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13189 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13203 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13203, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13210 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13210 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13246 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13246 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13282 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13282
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
                              let uu____13306 = combine t11 t21 wl2  in
                              (match uu____13306 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13339 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13339
                                     then
                                       let uu____13344 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13344
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13386 ts1 =
               match uu____13386 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13449 = pairwise out t wl2  in
                        (match uu____13449 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13485 =
               let uu____13496 = FStar_List.hd ts  in (uu____13496, [], wl1)
                in
             let uu____13505 = FStar_List.tl ts  in
             aux uu____13485 uu____13505  in
           let uu____13512 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13512 with
           | (this_flex,this_rigid) ->
               let uu____13538 =
                 let uu____13539 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13539.FStar_Syntax_Syntax.n  in
               (match uu____13538 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13564 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13564
                    then
                      let uu____13567 = destruct_flex_t this_flex wl  in
                      (match uu____13567 with
                       | (flex,wl1) ->
                           let uu____13574 = quasi_pattern env flex  in
                           (match uu____13574 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13593 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13593
                                  then
                                    let uu____13598 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13598
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13605 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1950_13608 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1950_13608.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1950_13608.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1950_13608.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1950_13608.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1950_13608.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1950_13608.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1950_13608.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1950_13608.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1950_13608.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13605)
                | uu____13609 ->
                    ((let uu____13611 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13611
                      then
                        let uu____13616 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13616
                      else ());
                     (let uu____13621 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13621 with
                      | (u,_args) ->
                          let uu____13664 =
                            let uu____13665 = FStar_Syntax_Subst.compress u
                               in
                            uu____13665.FStar_Syntax_Syntax.n  in
                          (match uu____13664 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13693 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13693 with
                                 | (u',uu____13712) ->
                                     let uu____13737 =
                                       let uu____13738 = whnf env u'  in
                                       uu____13738.FStar_Syntax_Syntax.n  in
                                     (match uu____13737 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13760 -> false)
                                  in
                               let uu____13762 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13785  ->
                                         match uu___26_13785 with
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
                                              | uu____13799 -> false)
                                         | uu____13803 -> false))
                                  in
                               (match uu____13762 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13818 = whnf env this_rigid
                                         in
                                      let uu____13819 =
                                        FStar_List.collect
                                          (fun uu___27_13825  ->
                                             match uu___27_13825 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13831 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13831]
                                             | uu____13835 -> [])
                                          bounds_probs
                                         in
                                      uu____13818 :: uu____13819  in
                                    let uu____13836 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13836 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13869 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13884 =
                                               let uu____13885 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13885.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13884 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13897 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13897)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13908 -> bound  in
                                           let uu____13909 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13909)  in
                                         (match uu____13869 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13944 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13944
                                                then
                                                  let wl'1 =
                                                    let uu___2010_13950 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2010_13950.wl_deferred);
                                                      ctr =
                                                        (uu___2010_13950.ctr);
                                                      defer_ok =
                                                        (uu___2010_13950.defer_ok);
                                                      smt_ok =
                                                        (uu___2010_13950.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2010_13950.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2010_13950.tcenv);
                                                      wl_implicits =
                                                        (uu___2010_13950.wl_implicits)
                                                    }  in
                                                  let uu____13951 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13951
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13957 =
                                                  solve_t env eq_prob
                                                    (let uu___2015_13959 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2015_13959.wl_deferred);
                                                       ctr =
                                                         (uu___2015_13959.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2015_13959.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2015_13959.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2015_13959.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13957 with
                                                | Success (uu____13961,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2021_13964 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2021_13964.wl_deferred);
                                                        ctr =
                                                          (uu___2021_13964.ctr);
                                                        defer_ok =
                                                          (uu___2021_13964.defer_ok);
                                                        smt_ok =
                                                          (uu___2021_13964.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2021_13964.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2021_13964.tcenv);
                                                        wl_implicits =
                                                          (uu___2021_13964.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2024_13966 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2024_13966.attempting);
                                                        wl_deferred =
                                                          (uu___2024_13966.wl_deferred);
                                                        ctr =
                                                          (uu___2024_13966.ctr);
                                                        defer_ok =
                                                          (uu___2024_13966.defer_ok);
                                                        smt_ok =
                                                          (uu___2024_13966.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2024_13966.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2024_13966.tcenv);
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
                                                    let uu____13982 =
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
                                                    ((let uu____13994 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13994
                                                      then
                                                        let uu____13999 =
                                                          let uu____14001 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____14001
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13999
                                                      else ());
                                                     (let uu____14014 =
                                                        let uu____14029 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14029)
                                                         in
                                                      match uu____14014 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14051))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14077 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14077
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
                                                                  let uu____14097
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14097))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14122 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14122
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
                                                                    let uu____14142
                                                                    =
                                                                    let uu____14147
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14147
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14142
                                                                    [] wl2
                                                                     in
                                                                  let uu____14153
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14153))))
                                                      | uu____14154 ->
                                                          let uu____14169 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14169 p)))))))
                           | uu____14176 when flip ->
                               let uu____14177 =
                                 let uu____14179 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14181 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14179 uu____14181
                                  in
                               failwith uu____14177
                           | uu____14184 ->
                               let uu____14185 =
                                 let uu____14187 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14189 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14187 uu____14189
                                  in
                               failwith uu____14185)))))

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
                      (fun uu____14225  ->
                         match uu____14225 with
                         | (x,i) ->
                             let uu____14244 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14244, i)) bs_lhs
                     in
                  let uu____14247 = lhs  in
                  match uu____14247 with
                  | (uu____14248,u_lhs,uu____14250) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14347 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14357 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14357, univ)
                             in
                          match uu____14347 with
                          | (k,univ) ->
                              let uu____14364 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14364 with
                               | (uu____14381,u,wl3) ->
                                   let uu____14384 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14384, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14410 =
                              let uu____14423 =
                                let uu____14434 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14434 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14485  ->
                                   fun uu____14486  ->
                                     match (uu____14485, uu____14486) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14587 =
                                           let uu____14594 =
                                             let uu____14597 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14597
                                              in
                                           copy_uvar u_lhs [] uu____14594 wl2
                                            in
                                         (match uu____14587 with
                                          | (uu____14626,t_a,wl3) ->
                                              let uu____14629 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14629 with
                                               | (uu____14648,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14423
                                ([], wl1)
                               in
                            (match uu____14410 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2135_14704 = ct  in
                                   let uu____14705 =
                                     let uu____14708 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14708
                                      in
                                   let uu____14723 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2135_14704.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2135_14704.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14705;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14723;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2135_14704.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2138_14741 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2138_14741.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2138_14741.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14744 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14744 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14806 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14806 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14817 =
                                          let uu____14822 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14822)  in
                                        TERM uu____14817  in
                                      let uu____14823 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14823 with
                                       | (sub_prob,wl3) ->
                                           let uu____14837 =
                                             let uu____14838 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14838
                                              in
                                           solve env uu____14837))
                             | (x,imp)::formals2 ->
                                 let uu____14860 =
                                   let uu____14867 =
                                     let uu____14870 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14870
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14867 wl1
                                    in
                                 (match uu____14860 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14891 =
                                          let uu____14894 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14894
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14891 u_x
                                         in
                                      let uu____14895 =
                                        let uu____14898 =
                                          let uu____14901 =
                                            let uu____14902 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14902, imp)  in
                                          [uu____14901]  in
                                        FStar_List.append bs_terms
                                          uu____14898
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14895 formals2 wl2)
                              in
                           let uu____14929 = occurs_check u_lhs arrow1  in
                           (match uu____14929 with
                            | (uu____14942,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14958 =
                                    FStar_Thunk.mk
                                      (fun uu____14962  ->
                                         let uu____14963 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14963)
                                     in
                                  giveup_or_defer env orig wl uu____14958
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
              (let uu____14996 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14996
               then
                 let uu____15001 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____15004 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15001 (rel_to_string (p_rel orig)) uu____15004
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15135 = rhs wl1 scope env1 subst1  in
                     (match uu____15135 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15158 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15158
                            then
                              let uu____15163 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15163
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15241 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15241 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2208_15243 = hd1  in
                       let uu____15244 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2208_15243.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2208_15243.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15244
                       }  in
                     let hd21 =
                       let uu___2211_15248 = hd2  in
                       let uu____15249 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2211_15248.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2211_15248.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15249
                       }  in
                     let uu____15252 =
                       let uu____15257 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15257
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15252 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15280 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15280
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15287 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15287 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15359 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15359
                                  in
                               ((let uu____15377 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15377
                                 then
                                   let uu____15382 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15384 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15382
                                     uu____15384
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15419 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15455 = aux wl [] env [] bs1 bs2  in
               match uu____15455 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15514 = attempt sub_probs wl2  in
                   solve env1 uu____15514)

and (try_solve_without_smt_or_else :
  FStar_TypeChecker_Env.env ->
    worklist ->
      (FStar_TypeChecker_Env.env -> worklist -> solution) ->
        (FStar_TypeChecker_Env.env ->
           worklist -> (FStar_TypeChecker_Common.prob * lstring) -> solution)
          -> solution)
  =
  fun env  ->
    fun wl  ->
      fun try_solve  ->
        fun else_solve  ->
          let wl' =
            let uu___2249_15534 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2249_15534.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2249_15534.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15546 = try_solve env wl'  in
          match uu____15546 with
          | Success (uu____15547,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2258_15551 = wl  in
                  {
                    attempting = (uu___2258_15551.attempting);
                    wl_deferred = (uu___2258_15551.wl_deferred);
                    ctr = (uu___2258_15551.ctr);
                    defer_ok = (uu___2258_15551.defer_ok);
                    smt_ok = (uu___2258_15551.smt_ok);
                    umax_heuristic_ok = (uu___2258_15551.umax_heuristic_ok);
                    tcenv = (uu___2258_15551.tcenv);
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
        (let uu____15560 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15560 wl)

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
              let uu____15574 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15574 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15608 = lhs1  in
              match uu____15608 with
              | (uu____15611,ctx_u,uu____15613) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15621 ->
                        let uu____15622 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15622 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15671 = quasi_pattern env1 lhs1  in
              match uu____15671 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15705) ->
                  let uu____15710 = lhs1  in
                  (match uu____15710 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15725 = occurs_check ctx_u rhs1  in
                       (match uu____15725 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15776 =
                                let uu____15784 =
                                  let uu____15786 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15786
                                   in
                                FStar_Util.Inl uu____15784  in
                              (uu____15776, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15814 =
                                 let uu____15816 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15816  in
                               if uu____15814
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15843 =
                                    let uu____15851 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15851  in
                                  let uu____15857 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15843, uu____15857)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15901 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15901 with
              | (rhs_hd,args) ->
                  let uu____15944 = FStar_Util.prefix args  in
                  (match uu____15944 with
                   | (args_rhs,last_arg_rhs) ->
                       let uu____16013 = last_arg_rhs  in
                       (match uu____16013 with
                        | (last_arg_rhs1,iqual_last_arg_rhs) ->
                            let rhs' =
                              FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                                FStar_Pervasives_Native.None
                                rhs1.FStar_Syntax_Syntax.pos
                               in
                            let uu____16035 = lhs1  in
                            (match uu____16035 with
                             | (t_lhs,u_lhs,lhs_args) ->
                                 let uu____16039 =
                                   let uu____16046 =
                                     let uu____16049 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____16049
                                      in
                                   copy_uvar_for_type u_lhs [] uu____16046
                                     wl1
                                    in
                                 (match uu____16039 with
                                  | (uu____16072,t_last_arg,wl2) ->
                                      let uu____16075 =
                                        let uu____16082 =
                                          let uu____16085 =
                                            let uu____16094 =
                                              let uu____16103 =
                                                let uu____16110 =
                                                  FStar_Syntax_Syntax.null_bv
                                                    t_last_arg
                                                   in
                                                (uu____16110,
                                                  iqual_last_arg_rhs)
                                                 in
                                              [uu____16103]  in
                                            FStar_List.append bs_lhs
                                              uu____16094
                                             in
                                          let uu____16131 =
                                            FStar_Syntax_Syntax.mk_Total
                                              t_res_lhs
                                             in
                                          FStar_Syntax_Util.arrow uu____16085
                                            uu____16131
                                           in
                                        copy_uvar u_lhs [] uu____16082 wl2
                                         in
                                      (match uu____16075 with
                                       | (uu____16140,lhs',wl3) ->
                                           let uu____16143 =
                                             let uu____16150 =
                                               let uu____16153 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   t_last_arg
                                                  in
                                               FStar_Syntax_Util.arrow bs_lhs
                                                 uu____16153
                                                in
                                             copy_uvar u_lhs [] uu____16150
                                               wl3
                                              in
                                           (match uu____16143 with
                                            | (uu____16162,lhs'_last_arg,wl4)
                                                ->
                                                let sol =
                                                  let uu____16168 =
                                                    let uu____16169 =
                                                      let uu____16174 =
                                                        let uu____16175 =
                                                          let uu____16178 =
                                                            let uu____16183 =
                                                              FStar_Syntax_Util.mk_app_binders
                                                                lhs' bs_lhs
                                                               in
                                                            let uu____16184 =
                                                              let uu____16185
                                                                =
                                                                let uu____16194
                                                                  =
                                                                  FStar_Syntax_Util.mk_app_binders
                                                                    lhs'_last_arg
                                                                    bs_lhs
                                                                   in
                                                                (uu____16194,
                                                                  iqual_last_arg_rhs)
                                                                 in
                                                              [uu____16185]
                                                               in
                                                            FStar_Syntax_Syntax.mk_Tm_app
                                                              uu____16183
                                                              uu____16184
                                                             in
                                                          uu____16178
                                                            FStar_Pervasives_Native.None
                                                            lhs'.FStar_Syntax_Syntax.pos
                                                           in
                                                        FStar_Syntax_Util.abs
                                                          bs_lhs uu____16175
                                                          (FStar_Pervasives_Native.Some
                                                             (FStar_Syntax_Util.residual_tot
                                                                t_res_lhs))
                                                         in
                                                      (u_lhs, uu____16174)
                                                       in
                                                    TERM uu____16169  in
                                                  [uu____16168]  in
                                                let uu____16217 =
                                                  let uu____16224 =
                                                    let uu____16229 =
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        lhs' lhs_args
                                                        FStar_Pervasives_Native.None
                                                        lhs'.FStar_Syntax_Syntax.pos
                                                       in
                                                    mk_t_problem wl4 [] orig1
                                                      uu____16229
                                                      FStar_TypeChecker_Common.EQ
                                                      rhs'
                                                      FStar_Pervasives_Native.None
                                                      "first-order lhs"
                                                     in
                                                  match uu____16224 with
                                                  | (p1,wl5) ->
                                                      let uu____16245 =
                                                        let uu____16250 =
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            lhs'_last_arg
                                                            lhs_args
                                                            FStar_Pervasives_Native.None
                                                            lhs'_last_arg.FStar_Syntax_Syntax.pos
                                                           in
                                                        mk_t_problem wl5 []
                                                          orig1 uu____16250
                                                          FStar_TypeChecker_Common.EQ
                                                          last_arg_rhs1
                                                          FStar_Pervasives_Native.None
                                                          "first-order rhs"
                                                         in
                                                      (match uu____16245 with
                                                       | (p2,wl6) ->
                                                           ([p1; p2], wl6))
                                                   in
                                                (match uu____16217 with
                                                 | (sub_probs,wl5) ->
                                                     let uu____16274 =
                                                       let uu____16275 =
                                                         solve_prob orig1
                                                           FStar_Pervasives_Native.None
                                                           sol wl5
                                                          in
                                                       attempt sub_probs
                                                         uu____16275
                                                        in
                                                     solve env1 uu____16274)))))))
               in
            let first_order_applicable orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16337 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16337 with
                | (uu____16355,args) ->
                    (match args with | [] -> false | uu____16391 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16410 =
                  let uu____16411 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16411.FStar_Syntax_Syntax.n  in
                match uu____16410 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16415 -> true
                | uu____16431 -> false  in
              let uu____16433 = quasi_pattern env1 lhs1  in
              match uu____16433 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16476 = is_app rhs1  in
                  if uu____16476
                  then
                    FStar_Pervasives_Native.Some
                      (FStar_Util.Inl (bs_lhs, t_res_lhs))
                  else
                    (let uu____16515 = is_arrow rhs1  in
                     if uu____16515
                     then
                       FStar_Pervasives_Native.Some
                         (FStar_Util.Inr (bs_lhs, t_res_lhs))
                     else FStar_Pervasives_Native.None)
               in
            let apply_first_order orig1 env1 wl1 lhs1 rhs1 app_or_arrow =
              match app_or_arrow with
              | FStar_Util.Inl (bs_lhs,t_res_lhs) ->
                  imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
              | FStar_Util.Inr (bs_lhs,t_res_lhs) ->
                  imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                    FStar_TypeChecker_Common.EQ rhs1
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let uu____16667 =
                first_order_applicable orig1 env1 wl1 lhs1 rhs1  in
              match uu____16667 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    FStar_Thunk.mk
                      (fun uu____16701  ->
                         let uu____16702 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s"
                           uu____16702)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some app_or_arrow ->
                  apply_first_order orig1 env1 wl1 lhs1 rhs1 app_or_arrow
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16731 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16731
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16737 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16737
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16742 = lhs  in
                (match uu____16742 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16746 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16746 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16764 =
                              let uu____16768 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16768
                               in
                            FStar_All.pipe_right uu____16764
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16789 = occurs_check ctx_uv rhs1  in
                          (match uu____16789 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16818 =
                                   let uu____16819 =
                                     let uu____16821 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16821
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16819
                                    in
                                 giveup_or_defer env orig wl uu____16818
                               else
                                 (let fvs_included_ok =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  let ctx_included_ok =
                                    tgt_ctx_includes_all_source_ctx ctx_uv
                                      uvars1
                                     in
                                  if fvs_included_ok && ctx_included_ok
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let uu____16837 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl
                                       in
                                    solve env uu____16837
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         FStar_Thunk.mk
                                           (fun uu____16850  ->
                                              let uu____16851 =
                                                names_to_string1 fvs2  in
                                              let uu____16853 =
                                                names_to_string1 fvs1  in
                                              let uu____16855 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16851 uu____16853
                                                uu____16855)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else
                                      (let uu____16867 =
                                         first_order_applicable orig env wl
                                           lhs rhs1
                                          in
                                       match uu____16867 with
                                       | FStar_Pervasives_Native.None  ->
                                           if fvs_included_ok
                                           then
                                             let sol =
                                               mk_solution env lhs
                                                 lhs_binders rhs1
                                                in
                                             let wl1 =
                                               restrict_all_uvars ctx_uv
                                                 uvars1 wl
                                                in
                                             let uu____16899 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 sol wl1
                                                in
                                             solve env uu____16899
                                           else
                                             (let uu____16902 =
                                                FStar_All.pipe_left
                                                  FStar_Thunk.mkv
                                                  "free-variable check failed an firstorder imitation is not applicable either"
                                                 in
                                              giveup_or_defer env orig wl
                                                uu____16902)
                                       | FStar_Pervasives_Native.Some
                                           app_or_arrow ->
                                           apply_first_order orig env wl lhs
                                             rhs1 app_or_arrow)))
                      | uu____16931 ->
                          if wl.defer_ok
                          then
                            let uu____16935 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16935
                          else
                            (let uu____16940 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16940 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16966 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16966
                             | (FStar_Util.Inl msg,uu____16968) ->
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
                then
                  let uu____16986 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16986
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16992 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16992
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____17014 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____17014
                else
                  (let uu____17019 =
                     let uu____17036 = quasi_pattern env lhs  in
                     let uu____17043 = quasi_pattern env rhs  in
                     (uu____17036, uu____17043)  in
                   match uu____17019 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____17086 = lhs  in
                       (match uu____17086 with
                        | ({ FStar_Syntax_Syntax.n = uu____17087;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____17089;_},u_lhs,uu____17091)
                            ->
                            let uu____17094 = rhs  in
                            (match uu____17094 with
                             | (uu____17095,u_rhs,uu____17097) ->
                                 let uu____17098 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____17098
                                 then
                                   let uu____17105 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____17105
                                 else
                                   (let uu____17108 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____17108 with
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
                                        let uu____17140 =
                                          let uu____17147 =
                                            let uu____17150 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____17150
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____17147
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____17140 with
                                         | (uu____17162,w,wl1) ->
                                             let w_app =
                                               let uu____17168 =
                                                 let uu____17173 =
                                                   FStar_List.map
                                                     (fun uu____17184  ->
                                                        match uu____17184
                                                        with
                                                        | (z,uu____17192) ->
                                                            let uu____17197 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____17197) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____17173
                                                  in
                                               uu____17168
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____17199 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____17199
                                               then
                                                 let uu____17204 =
                                                   let uu____17208 =
                                                     flex_t_to_string lhs  in
                                                   let uu____17210 =
                                                     let uu____17214 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____17216 =
                                                       let uu____17220 =
                                                         term_to_string w  in
                                                       let uu____17222 =
                                                         let uu____17226 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____17235 =
                                                           let uu____17239 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____17248 =
                                                             let uu____17252
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____17252]
                                                              in
                                                           uu____17239 ::
                                                             uu____17248
                                                            in
                                                         uu____17226 ::
                                                           uu____17235
                                                          in
                                                       uu____17220 ::
                                                         uu____17222
                                                        in
                                                     uu____17214 ::
                                                       uu____17216
                                                      in
                                                   uu____17208 :: uu____17210
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____17204
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____17269 =
                                                     let uu____17274 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____17274)  in
                                                   TERM uu____17269  in
                                                 let uu____17275 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____17275
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____17283 =
                                                        let uu____17288 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____17288)
                                                         in
                                                      TERM uu____17283  in
                                                    [s1; s2])
                                                  in
                                               let uu____17289 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____17289))))))
                   | uu____17290 ->
                       let uu____17307 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____17307)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17361 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____17361
            then
              let uu____17366 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17368 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17370 = FStar_Syntax_Print.term_to_string t2  in
              let uu____17372 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17366 uu____17368 uu____17370 uu____17372
            else ());
           (let uu____17383 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17383 with
            | (head1,args1) ->
                let uu____17426 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17426 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17496 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17496 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17501 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17501)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17522 =
                         FStar_Thunk.mk
                           (fun uu____17529  ->
                              let uu____17530 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17532 = args_to_string args1  in
                              let uu____17536 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17538 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17530 uu____17532 uu____17536
                                uu____17538)
                          in
                       giveup env1 uu____17522 orig
                     else
                       (let uu____17545 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17550 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17550 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17545
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2542_17554 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2542_17554.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2542_17554.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2542_17554.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2542_17554.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2542_17554.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2542_17554.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2542_17554.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2542_17554.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17564 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17564
                                    else solve env1 wl2))
                        else
                          (let uu____17569 = base_and_refinement env1 t1  in
                           match uu____17569 with
                           | (base1,refinement1) ->
                               let uu____17594 = base_and_refinement env1 t2
                                  in
                               (match uu____17594 with
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
                                           let uu____17759 =
                                             FStar_List.fold_right
                                               (fun uu____17799  ->
                                                  fun uu____17800  ->
                                                    match (uu____17799,
                                                            uu____17800)
                                                    with
                                                    | (((a1,uu____17852),
                                                        (a2,uu____17854)),
                                                       (probs,wl3)) ->
                                                        let uu____17903 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17903
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17759 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17946 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17946
                                                 then
                                                   let uu____17951 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17951
                                                 else ());
                                                (let uu____17957 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17957
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
                                                    (let uu____17984 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17984 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____18000 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18000
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____18008 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____18008))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____18033 =
                                                    mk_sub_probs wl3  in
                                                  match uu____18033 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____18049 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____18049
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____18057 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____18057)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____18085 =
                                           match uu____18085 with
                                           | (prob,reason) ->
                                               ((let uu____18102 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18102
                                                 then
                                                   let uu____18107 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____18109 =
                                                     prob_to_string env2 prob
                                                      in
                                                   let uu____18111 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____18107 uu____18109
                                                     uu____18111
                                                 else ());
                                                (let uu____18117 =
                                                   let uu____18126 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____18129 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____18126, uu____18129)
                                                    in
                                                 match uu____18117 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____18142 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____18142 with
                                                      | (head1',uu____18160)
                                                          ->
                                                          let uu____18185 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____18185
                                                           with
                                                           | (head2',uu____18203)
                                                               ->
                                                               let uu____18228
                                                                 =
                                                                 let uu____18233
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____18234
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____18233,
                                                                   uu____18234)
                                                                  in
                                                               (match uu____18228
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____18236
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18236
                                                                    then
                                                                    let uu____18241
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____18243
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____18245
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____18247
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____18241
                                                                    uu____18243
                                                                    uu____18245
                                                                    uu____18247
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18252
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2630_18260
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2630_18260.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2630_18260.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2630_18260.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2630_18260.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2630_18260.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2630_18260.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2630_18260.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2630_18260.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____18262
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18262
                                                                    then
                                                                    let uu____18267
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18267
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18272 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____18284 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____18284 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____18292 =
                                             let uu____18293 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____18293.FStar_Syntax_Syntax.n
                                              in
                                           match uu____18292 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18298 -> false  in
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
                                          | uu____18301 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18304 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2650_18340 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2650_18340.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2650_18340.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2650_18340.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2650_18340.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2650_18340.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2650_18340.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2650_18340.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2650_18340.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18416 = destruct_flex_t scrutinee wl1  in
             match uu____18416 with
             | ((_t,uv,_args),wl2) ->
                 let uu____18427 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18427 with
                  | (xs,pat_term,uu____18443,uu____18444) ->
                      let uu____18449 =
                        FStar_List.fold_left
                          (fun uu____18472  ->
                             fun x  ->
                               match uu____18472 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18493 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18493 with
                                    | (uu____18512,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____18449 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18533 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18533 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2690_18550 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2690_18550.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2690_18550.umax_heuristic_ok);
                                    tcenv = (uu___2690_18550.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18561 = solve env1 wl'  in
                                (match uu____18561 with
                                 | Success (uu____18564,imps) ->
                                     let wl'1 =
                                       let uu___2698_18567 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2698_18567.wl_deferred);
                                         ctr = (uu___2698_18567.ctr);
                                         defer_ok =
                                           (uu___2698_18567.defer_ok);
                                         smt_ok = (uu___2698_18567.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2698_18567.umax_heuristic_ok);
                                         tcenv = (uu___2698_18567.tcenv);
                                         wl_implicits =
                                           (uu___2698_18567.wl_implicits)
                                       }  in
                                     let uu____18568 = solve env1 wl'1  in
                                     (match uu____18568 with
                                      | Success (uu____18571,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2706_18575 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2706_18575.attempting);
                                                 wl_deferred =
                                                   (uu___2706_18575.wl_deferred);
                                                 ctr = (uu___2706_18575.ctr);
                                                 defer_ok =
                                                   (uu___2706_18575.defer_ok);
                                                 smt_ok =
                                                   (uu___2706_18575.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2706_18575.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2706_18575.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18576 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18582 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18605 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18605
                 then
                   let uu____18610 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18612 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18610 uu____18612
                 else ());
                (let uu____18617 =
                   let uu____18638 =
                     let uu____18647 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18647)  in
                   let uu____18654 =
                     let uu____18663 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18663)  in
                   (uu____18638, uu____18654)  in
                 match uu____18617 with
                 | ((uu____18693,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18696;
                                   FStar_Syntax_Syntax.vars = uu____18697;_}),
                    (s,t)) ->
                     let uu____18768 =
                       let uu____18770 = is_flex scrutinee  in
                       Prims.op_Negation uu____18770  in
                     if uu____18768
                     then
                       ((let uu____18781 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18781
                         then
                           let uu____18786 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18786
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18805 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18805
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18820 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18820
                           then
                             let uu____18825 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18827 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18825 uu____18827
                           else ());
                          (let pat_discriminates uu___28_18852 =
                             match uu___28_18852 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18868;
                                  FStar_Syntax_Syntax.p = uu____18869;_},FStar_Pervasives_Native.None
                                ,uu____18870) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18884;
                                  FStar_Syntax_Syntax.p = uu____18885;_},FStar_Pervasives_Native.None
                                ,uu____18886) -> true
                             | uu____18913 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19016 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19016 with
                                       | (uu____19018,uu____19019,t') ->
                                           let uu____19037 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19037 with
                                            | (FullMatch ,uu____19049) ->
                                                true
                                            | (HeadMatch
                                               uu____19063,uu____19064) ->
                                                true
                                            | uu____19079 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19116 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19116
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19127 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19127 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19215,uu____19216) ->
                                       branches1
                                   | uu____19361 -> branches  in
                                 let uu____19416 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19425 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19425 with
                                        | (p,uu____19429,uu____19430) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19459  -> FStar_Util.Inr _19459)
                                   uu____19416))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19489 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19489 with
                                | (p,uu____19498,e) ->
                                    ((let uu____19517 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19517
                                      then
                                        let uu____19522 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19524 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19522 uu____19524
                                      else ());
                                     (let uu____19529 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19544  -> FStar_Util.Inr _19544)
                                        uu____19529)))))
                 | ((s,t),(uu____19547,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19550;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19551;_}))
                     ->
                     let uu____19620 =
                       let uu____19622 = is_flex scrutinee  in
                       Prims.op_Negation uu____19622  in
                     if uu____19620
                     then
                       ((let uu____19633 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19633
                         then
                           let uu____19638 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19638
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19657 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19657
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19672 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19672
                           then
                             let uu____19677 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19679 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19677 uu____19679
                           else ());
                          (let pat_discriminates uu___28_19704 =
                             match uu___28_19704 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19720;
                                  FStar_Syntax_Syntax.p = uu____19721;_},FStar_Pervasives_Native.None
                                ,uu____19722) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19736;
                                  FStar_Syntax_Syntax.p = uu____19737;_},FStar_Pervasives_Native.None
                                ,uu____19738) -> true
                             | uu____19765 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19868 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19868 with
                                       | (uu____19870,uu____19871,t') ->
                                           let uu____19889 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19889 with
                                            | (FullMatch ,uu____19901) ->
                                                true
                                            | (HeadMatch
                                               uu____19915,uu____19916) ->
                                                true
                                            | uu____19931 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19968 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19968
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19979 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19979 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____20067,uu____20068) ->
                                       branches1
                                   | uu____20213 -> branches  in
                                 let uu____20268 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____20277 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____20277 with
                                        | (p,uu____20281,uu____20282) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _20311  -> FStar_Util.Inr _20311)
                                   uu____20268))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20341 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20341 with
                                | (p,uu____20350,e) ->
                                    ((let uu____20369 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20369
                                      then
                                        let uu____20374 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20376 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20374 uu____20376
                                      else ());
                                     (let uu____20381 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _20396  -> FStar_Util.Inr _20396)
                                        uu____20381)))))
                 | uu____20397 ->
                     ((let uu____20419 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20419
                       then
                         let uu____20424 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20426 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20424 uu____20426
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20472 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20472
            then
              let uu____20477 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20479 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20481 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20483 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20477 uu____20479 uu____20481 uu____20483
            else ());
           (let uu____20488 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20488 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20519,uu____20520) ->
                     let rec may_relate head3 =
                       let uu____20548 =
                         let uu____20549 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20549.FStar_Syntax_Syntax.n  in
                       match uu____20548 with
                       | FStar_Syntax_Syntax.Tm_name uu____20553 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20555 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20580 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20580 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20582 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20585
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20586 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20589,uu____20590) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20632) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20638) ->
                           may_relate t
                       | uu____20643 -> false  in
                     let uu____20645 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20645 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20658 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20658
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20668 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20668
                          then
                            let uu____20671 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20671 with
                             | (guard,wl2) ->
                                 let uu____20678 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20678)
                          else
                            (let uu____20681 =
                               FStar_Thunk.mk
                                 (fun uu____20688  ->
                                    let uu____20689 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20691 =
                                      let uu____20693 =
                                        let uu____20697 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20697
                                          (fun x  ->
                                             let uu____20704 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20704)
                                         in
                                      FStar_Util.dflt "" uu____20693  in
                                    let uu____20709 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20711 =
                                      let uu____20713 =
                                        let uu____20717 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20717
                                          (fun x  ->
                                             let uu____20724 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20724)
                                         in
                                      FStar_Util.dflt "" uu____20713  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20689 uu____20691 uu____20709
                                      uu____20711)
                                in
                             giveup env1 uu____20681 orig))
                 | (HeadMatch (true ),uu____20730) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20745 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20745 with
                        | (guard,wl2) ->
                            let uu____20752 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20752)
                     else
                       (let uu____20755 =
                          FStar_Thunk.mk
                            (fun uu____20760  ->
                               let uu____20761 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20763 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20761 uu____20763)
                           in
                        giveup env1 uu____20755 orig)
                 | (uu____20766,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2881_20780 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2881_20780.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2881_20780.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2881_20780.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2881_20780.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2881_20780.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2881_20780.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2881_20780.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2881_20780.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20807 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20807
          then
            let uu____20810 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20810
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20816 =
                let uu____20819 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20819  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20816 t1);
             (let uu____20838 =
                let uu____20841 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20841  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20838 t2);
             (let uu____20860 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20860
              then
                let uu____20864 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20866 =
                  let uu____20868 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20870 =
                    let uu____20872 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20872  in
                  Prims.op_Hat uu____20868 uu____20870  in
                let uu____20875 =
                  let uu____20877 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20879 =
                    let uu____20881 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20881  in
                  Prims.op_Hat uu____20877 uu____20879  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20864 uu____20866 uu____20875
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20888,uu____20889) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20913,FStar_Syntax_Syntax.Tm_delayed uu____20914) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20938,uu____20939) ->
                  let uu____20966 =
                    let uu___2912_20967 = problem  in
                    let uu____20968 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2912_20967.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20968;
                      FStar_TypeChecker_Common.relation =
                        (uu___2912_20967.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2912_20967.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2912_20967.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2912_20967.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2912_20967.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2912_20967.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2912_20967.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2912_20967.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20966 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20969,uu____20970) ->
                  let uu____20977 =
                    let uu___2918_20978 = problem  in
                    let uu____20979 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2918_20978.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20979;
                      FStar_TypeChecker_Common.relation =
                        (uu___2918_20978.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2918_20978.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2918_20978.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2918_20978.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2918_20978.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2918_20978.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2918_20978.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2918_20978.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20977 wl
              | (uu____20980,FStar_Syntax_Syntax.Tm_ascribed uu____20981) ->
                  let uu____21008 =
                    let uu___2924_21009 = problem  in
                    let uu____21010 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2924_21009.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2924_21009.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2924_21009.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21010;
                      FStar_TypeChecker_Common.element =
                        (uu___2924_21009.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2924_21009.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2924_21009.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2924_21009.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2924_21009.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2924_21009.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21008 wl
              | (uu____21011,FStar_Syntax_Syntax.Tm_meta uu____21012) ->
                  let uu____21019 =
                    let uu___2930_21020 = problem  in
                    let uu____21021 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2930_21020.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2930_21020.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2930_21020.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21021;
                      FStar_TypeChecker_Common.element =
                        (uu___2930_21020.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2930_21020.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2930_21020.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2930_21020.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2930_21020.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2930_21020.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21019 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____21023),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____21025)) ->
                  let uu____21034 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____21034
              | (FStar_Syntax_Syntax.Tm_bvar uu____21035,uu____21036) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____21038,FStar_Syntax_Syntax.Tm_bvar uu____21039) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_21109 =
                    match uu___29_21109 with
                    | [] -> c
                    | bs ->
                        let uu____21137 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____21137
                     in
                  let uu____21148 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____21148 with
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
                                    let uu____21297 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____21297
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
                  let mk_t t l uu___30_21386 =
                    match uu___30_21386 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21428 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21428 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21573 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21574 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21573
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21574 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21576,uu____21577) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21608 -> true
                    | uu____21628 -> false  in
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
                      (let uu____21688 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3032_21696 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3032_21696.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3032_21696.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3032_21696.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3032_21696.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3032_21696.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3032_21696.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3032_21696.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3032_21696.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3032_21696.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3032_21696.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3032_21696.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3032_21696.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3032_21696.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3032_21696.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3032_21696.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3032_21696.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3032_21696.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3032_21696.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3032_21696.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3032_21696.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3032_21696.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3032_21696.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3032_21696.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3032_21696.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3032_21696.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3032_21696.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3032_21696.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3032_21696.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3032_21696.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3032_21696.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3032_21696.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3032_21696.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3032_21696.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3032_21696.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3032_21696.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3032_21696.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3032_21696.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3032_21696.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3032_21696.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3032_21696.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3032_21696.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3032_21696.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3032_21696.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3032_21696.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21688 with
                       | (uu____21701,ty,uu____21703) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21712 =
                                 let uu____21713 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21713.FStar_Syntax_Syntax.n  in
                               match uu____21712 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21716 ->
                                   let uu____21723 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21723
                               | uu____21724 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21727 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21727
                             then
                               let uu____21732 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21734 =
                                 let uu____21736 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21736
                                  in
                               let uu____21737 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21732 uu____21734 uu____21737
                             else ());
                            r1))
                     in
                  let uu____21742 =
                    let uu____21759 = maybe_eta t1  in
                    let uu____21766 = maybe_eta t2  in
                    (uu____21759, uu____21766)  in
                  (match uu____21742 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3053_21808 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3053_21808.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3053_21808.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3053_21808.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3053_21808.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3053_21808.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3053_21808.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3053_21808.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3053_21808.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21829 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21829
                       then
                         let uu____21832 = destruct_flex_t not_abs wl  in
                         (match uu____21832 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3070_21849 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3070_21849.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3070_21849.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3070_21849.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3070_21849.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3070_21849.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3070_21849.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3070_21849.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3070_21849.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21852 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21852 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21875 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21875
                       then
                         let uu____21878 = destruct_flex_t not_abs wl  in
                         (match uu____21878 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3070_21895 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3070_21895.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3070_21895.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3070_21895.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3070_21895.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3070_21895.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3070_21895.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3070_21895.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3070_21895.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21898 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21898 orig))
                   | uu____21901 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21919,FStar_Syntax_Syntax.Tm_abs uu____21920) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21951 -> true
                    | uu____21971 -> false  in
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
                      (let uu____22031 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3032_22039 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3032_22039.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3032_22039.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3032_22039.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3032_22039.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3032_22039.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3032_22039.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3032_22039.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3032_22039.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3032_22039.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3032_22039.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3032_22039.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3032_22039.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3032_22039.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3032_22039.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3032_22039.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3032_22039.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3032_22039.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3032_22039.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3032_22039.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3032_22039.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3032_22039.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3032_22039.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3032_22039.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3032_22039.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3032_22039.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3032_22039.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3032_22039.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3032_22039.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3032_22039.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3032_22039.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3032_22039.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3032_22039.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3032_22039.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3032_22039.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3032_22039.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3032_22039.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3032_22039.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3032_22039.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3032_22039.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3032_22039.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3032_22039.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3032_22039.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3032_22039.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3032_22039.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____22031 with
                       | (uu____22044,ty,uu____22046) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____22055 =
                                 let uu____22056 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____22056.FStar_Syntax_Syntax.n  in
                               match uu____22055 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22059 ->
                                   let uu____22066 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____22066
                               | uu____22067 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____22070 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____22070
                             then
                               let uu____22075 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____22077 =
                                 let uu____22079 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22079
                                  in
                               let uu____22080 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22075 uu____22077 uu____22080
                             else ());
                            r1))
                     in
                  let uu____22085 =
                    let uu____22102 = maybe_eta t1  in
                    let uu____22109 = maybe_eta t2  in
                    (uu____22102, uu____22109)  in
                  (match uu____22085 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3053_22151 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3053_22151.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3053_22151.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3053_22151.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3053_22151.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3053_22151.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3053_22151.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3053_22151.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3053_22151.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22172 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22172
                       then
                         let uu____22175 = destruct_flex_t not_abs wl  in
                         (match uu____22175 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3070_22192 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3070_22192.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3070_22192.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3070_22192.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3070_22192.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3070_22192.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3070_22192.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3070_22192.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3070_22192.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22195 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22195 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22218 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22218
                       then
                         let uu____22221 = destruct_flex_t not_abs wl  in
                         (match uu____22221 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3070_22238 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3070_22238.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3070_22238.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3070_22238.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3070_22238.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3070_22238.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3070_22238.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3070_22238.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3070_22238.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22241 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22241 orig))
                   | uu____22244 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____22274 =
                    let uu____22279 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____22279 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3093_22307 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3093_22307.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3093_22307.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3095_22309 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3095_22309.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3095_22309.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22310,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3093_22325 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3093_22325.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3093_22325.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3095_22327 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3095_22327.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3095_22327.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22328 -> (x1, x2)  in
                  (match uu____22274 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____22347 = as_refinement false env t11  in
                       (match uu____22347 with
                        | (x12,phi11) ->
                            let uu____22355 = as_refinement false env t21  in
                            (match uu____22355 with
                             | (x22,phi21) ->
                                 ((let uu____22364 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22364
                                   then
                                     ((let uu____22369 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____22371 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22373 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22369
                                         uu____22371 uu____22373);
                                      (let uu____22376 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____22378 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22380 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22376
                                         uu____22378 uu____22380))
                                   else ());
                                  (let uu____22385 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____22385 with
                                   | (base_prob,wl1) ->
                                       let x13 =
                                         FStar_Syntax_Syntax.freshen_bv x12
                                          in
                                       let subst1 =
                                         [FStar_Syntax_Syntax.DB
                                            (Prims.int_zero, x13)]
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
                                         let uu____22456 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22456
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22468 =
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
                                         (let uu____22481 =
                                            let uu____22484 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22484
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22481
                                            (p_guard base_prob));
                                         (let uu____22503 =
                                            let uu____22506 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22506
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22503
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22525 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22525)
                                          in
                                       let has_uvars =
                                         (let uu____22530 =
                                            let uu____22532 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22532
                                             in
                                          Prims.op_Negation uu____22530) ||
                                           (let uu____22536 =
                                              let uu____22538 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22538
                                               in
                                            Prims.op_Negation uu____22536)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22542 =
                                           let uu____22547 =
                                             let uu____22556 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22556]  in
                                           mk_t_problem wl1 uu____22547 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22542 with
                                          | (ref_prob,wl2) ->
                                              let uu____22578 =
                                                solve env1
                                                  (let uu___3137_22580 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3137_22580.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3137_22580.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3137_22580.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3137_22580.tcenv);
                                                     wl_implicits =
                                                       (uu___3137_22580.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22578 with
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
                                               | Success uu____22594 ->
                                                   let guard =
                                                     let uu____22602 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____22602
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3148_22611 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3148_22611.attempting);
                                                       wl_deferred =
                                                         (uu___3148_22611.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            Prims.int_one);
                                                       defer_ok =
                                                         (uu___3148_22611.defer_ok);
                                                       smt_ok =
                                                         (uu___3148_22611.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3148_22611.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3148_22611.tcenv);
                                                       wl_implicits =
                                                         (uu___3148_22611.wl_implicits)
                                                     }  in
                                                   let uu____22613 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____22613))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22616,FStar_Syntax_Syntax.Tm_uvar uu____22617) ->
                  let uu____22642 = destruct_flex_t t1 wl  in
                  (match uu____22642 with
                   | (f1,wl1) ->
                       let uu____22649 = destruct_flex_t t2 wl1  in
                       (match uu____22649 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22656;
                    FStar_Syntax_Syntax.pos = uu____22657;
                    FStar_Syntax_Syntax.vars = uu____22658;_},uu____22659),FStar_Syntax_Syntax.Tm_uvar
                 uu____22660) ->
                  let uu____22709 = destruct_flex_t t1 wl  in
                  (match uu____22709 with
                   | (f1,wl1) ->
                       let uu____22716 = destruct_flex_t t2 wl1  in
                       (match uu____22716 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22723,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22724;
                    FStar_Syntax_Syntax.pos = uu____22725;
                    FStar_Syntax_Syntax.vars = uu____22726;_},uu____22727))
                  ->
                  let uu____22776 = destruct_flex_t t1 wl  in
                  (match uu____22776 with
                   | (f1,wl1) ->
                       let uu____22783 = destruct_flex_t t2 wl1  in
                       (match uu____22783 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22790;
                    FStar_Syntax_Syntax.pos = uu____22791;
                    FStar_Syntax_Syntax.vars = uu____22792;_},uu____22793),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22794;
                    FStar_Syntax_Syntax.pos = uu____22795;
                    FStar_Syntax_Syntax.vars = uu____22796;_},uu____22797))
                  ->
                  let uu____22870 = destruct_flex_t t1 wl  in
                  (match uu____22870 with
                   | (f1,wl1) ->
                       let uu____22877 = destruct_flex_t t2 wl1  in
                       (match uu____22877 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22884,uu____22885) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22898 = destruct_flex_t t1 wl  in
                  (match uu____22898 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22905;
                    FStar_Syntax_Syntax.pos = uu____22906;
                    FStar_Syntax_Syntax.vars = uu____22907;_},uu____22908),uu____22909)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22946 = destruct_flex_t t1 wl  in
                  (match uu____22946 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22953,FStar_Syntax_Syntax.Tm_uvar uu____22954) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22967,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22968;
                    FStar_Syntax_Syntax.pos = uu____22969;
                    FStar_Syntax_Syntax.vars = uu____22970;_},uu____22971))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____23008,FStar_Syntax_Syntax.Tm_arrow uu____23009) ->
                  solve_t' env
                    (let uu___3248_23037 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3248_23037.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3248_23037.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3248_23037.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3248_23037.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3248_23037.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3248_23037.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3248_23037.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3248_23037.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3248_23037.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23038;
                    FStar_Syntax_Syntax.pos = uu____23039;
                    FStar_Syntax_Syntax.vars = uu____23040;_},uu____23041),FStar_Syntax_Syntax.Tm_arrow
                 uu____23042) ->
                  solve_t' env
                    (let uu___3248_23094 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3248_23094.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3248_23094.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3248_23094.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3248_23094.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3248_23094.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3248_23094.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3248_23094.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3248_23094.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3248_23094.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23095,FStar_Syntax_Syntax.Tm_uvar uu____23096) ->
                  let uu____23109 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23109
              | (uu____23110,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23111;
                    FStar_Syntax_Syntax.pos = uu____23112;
                    FStar_Syntax_Syntax.vars = uu____23113;_},uu____23114))
                  ->
                  let uu____23151 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23151
              | (FStar_Syntax_Syntax.Tm_uvar uu____23152,uu____23153) ->
                  let uu____23166 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23166
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23167;
                    FStar_Syntax_Syntax.pos = uu____23168;
                    FStar_Syntax_Syntax.vars = uu____23169;_},uu____23170),uu____23171)
                  ->
                  let uu____23208 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23208
              | (FStar_Syntax_Syntax.Tm_refine uu____23209,uu____23210) ->
                  let t21 =
                    let uu____23218 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____23218  in
                  solve_t env
                    (let uu___3283_23244 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3283_23244.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3283_23244.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3283_23244.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3283_23244.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3283_23244.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3283_23244.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3283_23244.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3283_23244.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3283_23244.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23245,FStar_Syntax_Syntax.Tm_refine uu____23246) ->
                  let t11 =
                    let uu____23254 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____23254  in
                  solve_t env
                    (let uu___3290_23280 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3290_23280.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3290_23280.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3290_23280.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3290_23280.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3290_23280.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3290_23280.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3290_23280.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3290_23280.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3290_23280.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____23362 =
                    let uu____23363 = guard_of_prob env wl problem t1 t2  in
                    match uu____23363 with
                    | (guard,wl1) ->
                        let uu____23370 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____23370
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23589 = br1  in
                        (match uu____23589 with
                         | (p1,w1,uu____23618) ->
                             let uu____23635 = br2  in
                             (match uu____23635 with
                              | (p2,w2,uu____23658) ->
                                  let uu____23663 =
                                    let uu____23665 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23665  in
                                  if uu____23663
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23692 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23692 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23729 = br2  in
                                         (match uu____23729 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23762 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23762
                                                 in
                                              let uu____23767 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23798,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23819) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23878 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23878 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23767
                                                (fun uu____23950  ->
                                                   match uu____23950 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23987 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23987
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____24008
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____24008
                                                              then
                                                                let uu____24013
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____24015
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____24013
                                                                  uu____24015
                                                              else ());
                                                             (let uu____24021
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____24021
                                                                (fun
                                                                   uu____24057
                                                                    ->
                                                                   match uu____24057
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
                    | uu____24186 -> FStar_Pervasives_Native.None  in
                  let uu____24227 = solve_branches wl brs1 brs2  in
                  (match uu____24227 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____24253 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____24253 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____24280 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____24280 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____24314 =
                                FStar_List.map
                                  (fun uu____24326  ->
                                     match uu____24326 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____24314  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____24335 =
                              let uu____24336 =
                                let uu____24337 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____24337
                                  (let uu___3389_24345 = wl3  in
                                   {
                                     attempting =
                                       (uu___3389_24345.attempting);
                                     wl_deferred =
                                       (uu___3389_24345.wl_deferred);
                                     ctr = (uu___3389_24345.ctr);
                                     defer_ok = (uu___3389_24345.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3389_24345.umax_heuristic_ok);
                                     tcenv = (uu___3389_24345.tcenv);
                                     wl_implicits =
                                       (uu___3389_24345.wl_implicits)
                                   })
                                 in
                              solve env uu____24336  in
                            (match uu____24335 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____24350 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24359 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____24359 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24362,uu____24363) ->
                  let head1 =
                    let uu____24387 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24387
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24433 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24433
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24479 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24479
                    then
                      let uu____24483 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24485 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24487 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24483 uu____24485 uu____24487
                    else ());
                   (let no_free_uvars t =
                      (let uu____24501 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24501) &&
                        (let uu____24505 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24505)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24524 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24524 = FStar_Syntax_Util.Equal  in
                    let uu____24525 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24525
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24529 = equal t1 t2  in
                         (if uu____24529
                          then
                            let uu____24532 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24532
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24537 =
                            let uu____24544 = equal t1 t2  in
                            if uu____24544
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24557 = mk_eq2 wl env orig t1 t2  in
                               match uu____24557 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24537 with
                          | (guard,wl1) ->
                              let uu____24578 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24578))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24581,uu____24582) ->
                  let head1 =
                    let uu____24590 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24590
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24636 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24636
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24682 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24682
                    then
                      let uu____24686 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24688 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24690 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24686 uu____24688 uu____24690
                    else ());
                   (let no_free_uvars t =
                      (let uu____24704 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24704) &&
                        (let uu____24708 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24708)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24727 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24727 = FStar_Syntax_Util.Equal  in
                    let uu____24728 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24728
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24732 = equal t1 t2  in
                         (if uu____24732
                          then
                            let uu____24735 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24735
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24740 =
                            let uu____24747 = equal t1 t2  in
                            if uu____24747
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24760 = mk_eq2 wl env orig t1 t2  in
                               match uu____24760 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24740 with
                          | (guard,wl1) ->
                              let uu____24781 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24781))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24784,uu____24785) ->
                  let head1 =
                    let uu____24787 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24787
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24833 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24833
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24879 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24879
                    then
                      let uu____24883 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24885 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24887 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24883 uu____24885 uu____24887
                    else ());
                   (let no_free_uvars t =
                      (let uu____24901 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24901) &&
                        (let uu____24905 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24905)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24924 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24924 = FStar_Syntax_Util.Equal  in
                    let uu____24925 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24925
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24929 = equal t1 t2  in
                         (if uu____24929
                          then
                            let uu____24932 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24932
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24937 =
                            let uu____24944 = equal t1 t2  in
                            if uu____24944
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24957 = mk_eq2 wl env orig t1 t2  in
                               match uu____24957 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24937 with
                          | (guard,wl1) ->
                              let uu____24978 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24978))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24981,uu____24982) ->
                  let head1 =
                    let uu____24984 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24984
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25030 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25030
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25076 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25076
                    then
                      let uu____25080 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25082 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25084 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25080 uu____25082 uu____25084
                    else ());
                   (let no_free_uvars t =
                      (let uu____25098 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25098) &&
                        (let uu____25102 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25102)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25121 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25121 = FStar_Syntax_Util.Equal  in
                    let uu____25122 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25122
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25126 = equal t1 t2  in
                         (if uu____25126
                          then
                            let uu____25129 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25129
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25134 =
                            let uu____25141 = equal t1 t2  in
                            if uu____25141
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25154 = mk_eq2 wl env orig t1 t2  in
                               match uu____25154 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25134 with
                          | (guard,wl1) ->
                              let uu____25175 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25175))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____25178,uu____25179) ->
                  let head1 =
                    let uu____25181 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25181
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25227 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25227
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25273 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25273
                    then
                      let uu____25277 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25279 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25281 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25277 uu____25279 uu____25281
                    else ());
                   (let no_free_uvars t =
                      (let uu____25295 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25295) &&
                        (let uu____25299 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25299)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25318 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25318 = FStar_Syntax_Util.Equal  in
                    let uu____25319 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25319
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25323 = equal t1 t2  in
                         (if uu____25323
                          then
                            let uu____25326 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25326
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25331 =
                            let uu____25338 = equal t1 t2  in
                            if uu____25338
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25351 = mk_eq2 wl env orig t1 t2  in
                               match uu____25351 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25331 with
                          | (guard,wl1) ->
                              let uu____25372 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25372))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25375,uu____25376) ->
                  let head1 =
                    let uu____25394 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25394
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25440 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25440
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25486 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25486
                    then
                      let uu____25490 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25492 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25494 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25490 uu____25492 uu____25494
                    else ());
                   (let no_free_uvars t =
                      (let uu____25508 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25508) &&
                        (let uu____25512 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25512)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25531 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25531 = FStar_Syntax_Util.Equal  in
                    let uu____25532 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25532
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25536 = equal t1 t2  in
                         (if uu____25536
                          then
                            let uu____25539 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25539
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25544 =
                            let uu____25551 = equal t1 t2  in
                            if uu____25551
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25564 = mk_eq2 wl env orig t1 t2  in
                               match uu____25564 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25544 with
                          | (guard,wl1) ->
                              let uu____25585 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25585))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25588,FStar_Syntax_Syntax.Tm_match uu____25589) ->
                  let head1 =
                    let uu____25613 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25613
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25659 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25659
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
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25750 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25750 = FStar_Syntax_Util.Equal  in
                    let uu____25751 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25751
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25755 = equal t1 t2  in
                         (if uu____25755
                          then
                            let uu____25758 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25758
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25763 =
                            let uu____25770 = equal t1 t2  in
                            if uu____25770
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25783 = mk_eq2 wl env orig t1 t2  in
                               match uu____25783 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25763 with
                          | (guard,wl1) ->
                              let uu____25804 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25804))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25807,FStar_Syntax_Syntax.Tm_uinst uu____25808) ->
                  let head1 =
                    let uu____25816 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25816
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25862 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25862
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25908 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25908
                    then
                      let uu____25912 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25914 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25916 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25912 uu____25914 uu____25916
                    else ());
                   (let no_free_uvars t =
                      (let uu____25930 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25930) &&
                        (let uu____25934 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25934)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25953 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25953 = FStar_Syntax_Util.Equal  in
                    let uu____25954 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25954
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25958 = equal t1 t2  in
                         (if uu____25958
                          then
                            let uu____25961 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25961
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25966 =
                            let uu____25973 = equal t1 t2  in
                            if uu____25973
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25986 = mk_eq2 wl env orig t1 t2  in
                               match uu____25986 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25966 with
                          | (guard,wl1) ->
                              let uu____26007 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26007))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26010,FStar_Syntax_Syntax.Tm_name uu____26011) ->
                  let head1 =
                    let uu____26013 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26013
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26059 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26059
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26099 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26099
                    then
                      let uu____26103 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26105 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26107 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26103 uu____26105 uu____26107
                    else ());
                   (let no_free_uvars t =
                      (let uu____26121 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26121) &&
                        (let uu____26125 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26125)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26144 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26144 = FStar_Syntax_Util.Equal  in
                    let uu____26145 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26145
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26149 = equal t1 t2  in
                         (if uu____26149
                          then
                            let uu____26152 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26152
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26157 =
                            let uu____26164 = equal t1 t2  in
                            if uu____26164
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26177 = mk_eq2 wl env orig t1 t2  in
                               match uu____26177 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26157 with
                          | (guard,wl1) ->
                              let uu____26198 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26198))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26201,FStar_Syntax_Syntax.Tm_constant uu____26202) ->
                  let head1 =
                    let uu____26204 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26204
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26244 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26244
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26284 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26284
                    then
                      let uu____26288 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26290 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26292 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26288 uu____26290 uu____26292
                    else ());
                   (let no_free_uvars t =
                      (let uu____26306 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26306) &&
                        (let uu____26310 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26310)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26329 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26329 = FStar_Syntax_Util.Equal  in
                    let uu____26330 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26330
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26334 = equal t1 t2  in
                         (if uu____26334
                          then
                            let uu____26337 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26337
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26342 =
                            let uu____26349 = equal t1 t2  in
                            if uu____26349
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26362 = mk_eq2 wl env orig t1 t2  in
                               match uu____26362 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26342 with
                          | (guard,wl1) ->
                              let uu____26383 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26383))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26386,FStar_Syntax_Syntax.Tm_fvar uu____26387) ->
                  let head1 =
                    let uu____26389 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26389
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26435 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26435
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26481 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26481
                    then
                      let uu____26485 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26487 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26489 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26485 uu____26487 uu____26489
                    else ());
                   (let no_free_uvars t =
                      (let uu____26503 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26503) &&
                        (let uu____26507 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26507)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26526 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26526 = FStar_Syntax_Util.Equal  in
                    let uu____26527 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26527
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26531 = equal t1 t2  in
                         (if uu____26531
                          then
                            let uu____26534 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26534
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26539 =
                            let uu____26546 = equal t1 t2  in
                            if uu____26546
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26559 = mk_eq2 wl env orig t1 t2  in
                               match uu____26559 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26539 with
                          | (guard,wl1) ->
                              let uu____26580 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26580))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26583,FStar_Syntax_Syntax.Tm_app uu____26584) ->
                  let head1 =
                    let uu____26602 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26602
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26642 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26642
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26682 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26682
                    then
                      let uu____26686 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26688 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26690 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26686 uu____26688 uu____26690
                    else ());
                   (let no_free_uvars t =
                      (let uu____26704 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26704) &&
                        (let uu____26708 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26708)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26727 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26727 = FStar_Syntax_Util.Equal  in
                    let uu____26728 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26728
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26732 = equal t1 t2  in
                         (if uu____26732
                          then
                            let uu____26735 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26735
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26740 =
                            let uu____26747 = equal t1 t2  in
                            if uu____26747
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26760 = mk_eq2 wl env orig t1 t2  in
                               match uu____26760 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26740 with
                          | (guard,wl1) ->
                              let uu____26781 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26781))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26784,FStar_Syntax_Syntax.Tm_let uu____26785) ->
                  let uu____26812 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26812
                  then
                    let uu____26815 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26815
                  else
                    (let uu____26818 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26818 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26821,uu____26822) ->
                  let uu____26836 =
                    let uu____26842 =
                      let uu____26844 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26846 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26848 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26850 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26844 uu____26846 uu____26848 uu____26850
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26842)
                     in
                  FStar_Errors.raise_error uu____26836
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26854,FStar_Syntax_Syntax.Tm_let uu____26855) ->
                  let uu____26869 =
                    let uu____26875 =
                      let uu____26877 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26879 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26881 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26883 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26877 uu____26879 uu____26881 uu____26883
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26875)
                     in
                  FStar_Errors.raise_error uu____26869
                    t1.FStar_Syntax_Syntax.pos
              | uu____26887 ->
                  let uu____26892 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26892 orig))))

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
        let solve_eq c1_comp c2_comp g_lift =
          (let uu____26958 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26958
           then
             let uu____26963 =
               let uu____26965 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26965  in
             let uu____26966 =
               let uu____26968 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26968  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26963 uu____26966
           else ());
          (let uu____26972 =
             let uu____26974 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26974  in
           if uu____26972
           then
             let uu____26977 =
               FStar_Thunk.mk
                 (fun uu____26982  ->
                    let uu____26983 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26985 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26983 uu____26985)
                in
             giveup env uu____26977 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____27007 =
                  FStar_Thunk.mk
                    (fun uu____27012  ->
                       let uu____27013 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____27015 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____27013 uu____27015)
                   in
                giveup env uu____27007 orig)
             else
               (let uu____27020 =
                  FStar_List.fold_left2
                    (fun uu____27041  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____27041 with
                           | (univ_sub_probs,wl1) ->
                               let uu____27062 =
                                 let uu____27067 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____27068 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____27067
                                   FStar_TypeChecker_Common.EQ uu____27068
                                   "effect universes"
                                  in
                               (match uu____27062 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____27020 with
                | (univ_sub_probs,wl1) ->
                    let uu____27088 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____27088 with
                     | (ret_sub_prob,wl2) ->
                         let uu____27096 =
                           FStar_List.fold_right2
                             (fun uu____27133  ->
                                fun uu____27134  ->
                                  fun uu____27135  ->
                                    match (uu____27133, uu____27134,
                                            uu____27135)
                                    with
                                    | ((a1,uu____27179),(a2,uu____27181),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____27214 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____27214 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____27096 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____27241 =
                                  let uu____27244 =
                                    let uu____27247 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____27247
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____27244
                                   in
                                FStar_List.append univ_sub_probs uu____27241
                                 in
                              let guard =
                                let guard =
                                  let uu____27269 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____27269  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3541_27278 = wl3  in
                                {
                                  attempting = (uu___3541_27278.attempting);
                                  wl_deferred = (uu___3541_27278.wl_deferred);
                                  ctr = (uu___3541_27278.ctr);
                                  defer_ok = (uu___3541_27278.defer_ok);
                                  smt_ok = (uu___3541_27278.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3541_27278.umax_heuristic_ok);
                                  tcenv = (uu___3541_27278.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____27280 = attempt sub_probs wl5  in
                              solve env uu____27280))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____27298 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____27298
           then
             let uu____27303 =
               let uu____27305 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27305
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____27307 =
               let uu____27309 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27309
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27303 uu____27307
           else ());
          (let uu____27314 =
             let uu____27319 =
               let uu____27324 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27324
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____27319
               (fun uu____27341  ->
                  match uu____27341 with
                  | (c,g) ->
                      let uu____27352 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____27352, g))
              in
           match uu____27314 with
           | (c12,g_lift) ->
               ((let uu____27356 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____27356
                 then
                   let uu____27361 =
                     let uu____27363 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27363
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____27365 =
                     let uu____27367 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27367
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____27361 uu____27365
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3561_27377 = wl  in
                     {
                       attempting = (uu___3561_27377.attempting);
                       wl_deferred = (uu___3561_27377.wl_deferred);
                       ctr = (uu___3561_27377.ctr);
                       defer_ok = (uu___3561_27377.defer_ok);
                       smt_ok = (uu___3561_27377.smt_ok);
                       umax_heuristic_ok =
                         (uu___3561_27377.umax_heuristic_ok);
                       tcenv = (uu___3561_27377.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____27378 =
                     let rec is_uvar1 t =
                       let uu____27392 =
                         let uu____27393 = FStar_Syntax_Subst.compress t  in
                         uu____27393.FStar_Syntax_Syntax.n  in
                       match uu____27392 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____27397 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27412) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27418) ->
                           is_uvar1 t1
                       | uu____27443 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27477  ->
                          fun uu____27478  ->
                            fun uu____27479  ->
                              match (uu____27477, uu____27478, uu____27479)
                              with
                              | ((a1,uu____27523),(a2,uu____27525),(is_sub_probs,wl2))
                                  ->
                                  let uu____27558 = is_uvar1 a1  in
                                  if uu____27558
                                  then
                                    ((let uu____27568 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27568
                                      then
                                        let uu____27573 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27575 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27573 uu____27575
                                      else ());
                                     (let uu____27580 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27580 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____27378 with
                   | (is_sub_probs,wl2) ->
                       let uu____27608 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27608 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27616 =
                              let uu____27621 =
                                let uu____27622 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27622
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27621
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27616 with
                             | (uu____27629,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27640 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27642 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27640 s uu____27642
                                    in
                                 let uu____27645 =
                                   let uu____27674 =
                                     let uu____27675 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27675.FStar_Syntax_Syntax.n  in
                                   match uu____27674 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27735 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27735 with
                                        | (a::bs1,c3) ->
                                            let uu____27791 =
                                              let uu____27810 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27810
                                                (fun uu____27914  ->
                                                   match uu____27914 with
                                                   | (l1,l2) ->
                                                       let uu____27987 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27987))
                                               in
                                            (match uu____27791 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____28092 ->
                                       let uu____28093 =
                                         let uu____28099 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____28099)
                                          in
                                       FStar_Errors.raise_error uu____28093 r
                                    in
                                 (match uu____27645 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____28175 =
                                        let uu____28182 =
                                          let uu____28183 =
                                            let uu____28184 =
                                              let uu____28191 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____28191,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____28184
                                             in
                                          [uu____28183]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____28182
                                          (fun b  ->
                                             let uu____28207 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____28209 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____28211 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____28207 uu____28209
                                               uu____28211) r
                                         in
                                      (match uu____28175 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____28221 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____28221
                                             then
                                               let uu____28226 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____28235 =
                                                          let uu____28237 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____28237
                                                           in
                                                        Prims.op_Hat s
                                                          uu____28235) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____28226
                                             else ());
                                            (let wl4 =
                                               let uu___3633_28245 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3633_28245.attempting);
                                                 wl_deferred =
                                                   (uu___3633_28245.wl_deferred);
                                                 ctr = (uu___3633_28245.ctr);
                                                 defer_ok =
                                                   (uu___3633_28245.defer_ok);
                                                 smt_ok =
                                                   (uu___3633_28245.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3633_28245.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3633_28245.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____28270 =
                                                        let uu____28277 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____28277, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____28270) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____28294 =
                                               let f_sort_is =
                                                 let uu____28304 =
                                                   let uu____28305 =
                                                     let uu____28308 =
                                                       let uu____28309 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____28309.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____28308
                                                      in
                                                   uu____28305.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____28304 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____28320,uu____28321::is)
                                                     ->
                                                     let uu____28363 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____28363
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28396 ->
                                                     let uu____28397 =
                                                       let uu____28403 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28403)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28397 r
                                                  in
                                               let uu____28409 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28444  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28444
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28465 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28465
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28409
                                                in
                                             match uu____28294 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28490 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28490
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28491 =
                                                   let g_sort_is =
                                                     let uu____28501 =
                                                       let uu____28502 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28502.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28501 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28507,uu____28508::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28568 ->
                                                         let uu____28569 =
                                                           let uu____28575 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28575)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28569 r
                                                      in
                                                   let uu____28581 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28616  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28616
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28637
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28637
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28581
                                                    in
                                                 (match uu____28491 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28664 =
                                                          let uu____28669 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28670 =
                                                            let uu____28671 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28671
                                                             in
                                                          (uu____28669,
                                                            uu____28670)
                                                           in
                                                        match uu____28664
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28699 =
                                                          let uu____28702 =
                                                            let uu____28705 =
                                                              let uu____28708
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28708
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28705
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28702
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28699
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28732 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28732
                                                           in
                                                        match g_lift.FStar_TypeChecker_Common.guard_f
                                                        with
                                                        | FStar_TypeChecker_Common.Trivial
                                                             -> guard
                                                        | FStar_TypeChecker_Common.NonTrivial
                                                            f ->
                                                            FStar_Syntax_Util.mk_conj
                                                              guard f
                                                         in
                                                      let wl7 =
                                                        let uu____28743 =
                                                          let uu____28746 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28749  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28749)
                                                            uu____28746
                                                           in
                                                        solve_prob orig
                                                          uu____28743 [] wl6
                                                         in
                                                      let uu____28750 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28750))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28773 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28775 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28775]
              | x -> x  in
            let c12 =
              let uu___3699_28778 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3699_28778.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3699_28778.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3699_28778.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3699_28778.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28779 =
              let uu____28784 =
                FStar_All.pipe_right
                  (let uu___3702_28786 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3702_28786.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3702_28786.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3702_28786.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3702_28786.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28784
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28779
              (fun uu____28800  ->
                 match uu____28800 with
                 | (c,g) ->
                     let uu____28807 =
                       let uu____28809 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28809  in
                     if uu____28807
                     then
                       let uu____28812 =
                         let uu____28818 =
                           let uu____28820 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28822 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28820 uu____28822
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28818)
                          in
                       FStar_Errors.raise_error uu____28812 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28828 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28828
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28834 = lift_c1 ()  in
               solve_eq uu____28834 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28843  ->
                         match uu___31_28843 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28848 -> false))
                  in
               let uu____28850 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28880)::uu____28881,(wp2,uu____28883)::uu____28884)
                     -> (wp1, wp2)
                 | uu____28957 ->
                     let uu____28982 =
                       let uu____28988 =
                         let uu____28990 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28992 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28990 uu____28992
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28988)
                        in
                     FStar_Errors.raise_error uu____28982
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28850 with
               | (wpc1,wpc2) ->
                   let uu____29002 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____29002
                   then
                     let uu____29005 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29005 wl
                   else
                     (let uu____29009 =
                        let uu____29016 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____29016  in
                      match uu____29009 with
                      | (c2_decl,qualifiers) ->
                          let uu____29037 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____29037
                          then
                            let c1_repr =
                              let uu____29044 =
                                let uu____29045 =
                                  let uu____29046 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____29046  in
                                let uu____29047 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____29045 uu____29047
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____29044
                               in
                            let c2_repr =
                              let uu____29050 =
                                let uu____29051 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____29052 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____29051 uu____29052
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____29050
                               in
                            let uu____29054 =
                              let uu____29059 =
                                let uu____29061 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____29063 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____29061
                                  uu____29063
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____29059
                               in
                            (match uu____29054 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____29069 = attempt [prob] wl2  in
                                 solve env uu____29069)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____29089 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____29089
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____29112 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____29112
                                      then
                                        FStar_Util.print_string
                                          "Using trivial wp ... \n"
                                      else ());
                                     (let c1_univ =
                                        env.FStar_TypeChecker_Env.universe_of
                                          env
                                          c11.FStar_Syntax_Syntax.result_typ
                                         in
                                      let trivial =
                                        let uu____29122 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____29122 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____29129 =
                                        let uu____29136 =
                                          let uu____29137 =
                                            let uu____29154 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____29157 =
                                              let uu____29168 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____29168; wpc1_2]  in
                                            (uu____29154, uu____29157)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____29137
                                           in
                                        FStar_Syntax_Syntax.mk uu____29136
                                         in
                                      uu____29129
                                        FStar_Pervasives_Native.None r))
                                  else
                                    (let c2_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c21.FStar_Syntax_Syntax.result_typ
                                        in
                                     let stronger =
                                       FStar_All.pipe_right c2_decl
                                         FStar_Syntax_Util.get_stronger_vc_combinator
                                        in
                                     let uu____29217 =
                                       let uu____29224 =
                                         let uu____29225 =
                                           let uu____29242 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____29245 =
                                             let uu____29256 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____29265 =
                                               let uu____29276 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____29276; wpc1_2]  in
                                             uu____29256 :: uu____29265  in
                                           (uu____29242, uu____29245)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____29225
                                          in
                                       FStar_Syntax_Syntax.mk uu____29224  in
                                     uu____29217 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____29330 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____29330
                              then
                                let uu____29335 =
                                  let uu____29337 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____29337
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____29335
                              else ());
                             (let uu____29341 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____29341 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____29350 =
                                      let uu____29353 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _29356  ->
                                           FStar_Pervasives_Native.Some
                                             _29356) uu____29353
                                       in
                                    solve_prob orig uu____29350 [] wl1  in
                                  let uu____29357 = attempt [base_prob] wl2
                                     in
                                  solve env uu____29357))))
           in
        let uu____29358 = FStar_Util.physical_equality c1 c2  in
        if uu____29358
        then
          let uu____29361 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____29361
        else
          ((let uu____29365 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____29365
            then
              let uu____29370 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____29372 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29370
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29372
            else ());
           (let uu____29377 =
              let uu____29386 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29389 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29386, uu____29389)  in
            match uu____29377 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29407),FStar_Syntax_Syntax.Total
                    (t2,uu____29409)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29426 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29426 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29428,FStar_Syntax_Syntax.Total uu____29429) ->
                     let uu____29446 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29446 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29450),FStar_Syntax_Syntax.Total
                    (t2,uu____29452)) ->
                     let uu____29469 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29469 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29472),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29474)) ->
                     let uu____29491 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29491 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29494),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29496)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29513 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29513 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29516),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29518)) ->
                     let uu____29535 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29535 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29538,FStar_Syntax_Syntax.Comp uu____29539) ->
                     let uu____29548 =
                       let uu___3826_29551 = problem  in
                       let uu____29554 =
                         let uu____29555 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29555
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3826_29551.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29554;
                         FStar_TypeChecker_Common.relation =
                           (uu___3826_29551.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3826_29551.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3826_29551.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3826_29551.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3826_29551.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3826_29551.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3826_29551.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3826_29551.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29548 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29556,FStar_Syntax_Syntax.Comp uu____29557) ->
                     let uu____29566 =
                       let uu___3826_29569 = problem  in
                       let uu____29572 =
                         let uu____29573 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29573
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3826_29569.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29572;
                         FStar_TypeChecker_Common.relation =
                           (uu___3826_29569.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3826_29569.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3826_29569.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3826_29569.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3826_29569.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3826_29569.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3826_29569.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3826_29569.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29566 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29574,FStar_Syntax_Syntax.GTotal uu____29575) ->
                     let uu____29584 =
                       let uu___3838_29587 = problem  in
                       let uu____29590 =
                         let uu____29591 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29591
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3838_29587.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3838_29587.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3838_29587.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29590;
                         FStar_TypeChecker_Common.element =
                           (uu___3838_29587.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3838_29587.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3838_29587.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3838_29587.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3838_29587.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3838_29587.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29584 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29592,FStar_Syntax_Syntax.Total uu____29593) ->
                     let uu____29602 =
                       let uu___3838_29605 = problem  in
                       let uu____29608 =
                         let uu____29609 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29609
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3838_29605.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3838_29605.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3838_29605.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29608;
                         FStar_TypeChecker_Common.element =
                           (uu___3838_29605.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3838_29605.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3838_29605.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3838_29605.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3838_29605.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3838_29605.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29602 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29610,FStar_Syntax_Syntax.Comp uu____29611) ->
                     let uu____29612 =
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
                     if uu____29612
                     then
                       let uu____29615 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29615 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29622 =
                            let uu____29627 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29627
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29636 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29637 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29636, uu____29637))
                             in
                          match uu____29622 with
                          | (c1_comp1,c2_comp1) ->
                              solve_eq c1_comp1 c2_comp1
                                FStar_TypeChecker_Env.trivial_guard
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____29645 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29645
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29653 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29653 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29656 =
                                  FStar_Thunk.mk
                                    (fun uu____29661  ->
                                       let uu____29662 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29664 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29662 uu____29664)
                                   in
                                giveup env uu____29656 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29675 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29675 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29725 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29725 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29750 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29781  ->
                match uu____29781 with
                | (u1,u2) ->
                    let uu____29789 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29791 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29789 uu____29791))
         in
      FStar_All.pipe_right uu____29750 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let (guard_to_string :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> Prims.string)
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Common.guard_f),
              (g.FStar_TypeChecker_Common.deferred),
              (g.FStar_TypeChecker_Common.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29828,[])) when
          let uu____29855 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29855 -> "{}"
      | uu____29858 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29885 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29885
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29897 =
              FStar_List.map
                (fun uu____29910  ->
                   match uu____29910 with
                   | (uu____29917,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29897 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29928 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29928 imps
  
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
                  let uu____29985 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29985
                  then
                    let uu____29993 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29995 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29993
                      (rel_to_string rel) uu____29995
                  else "TOP"  in
                let uu____30001 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____30001 with
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
              let uu____30061 =
                let uu____30064 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _30067  -> FStar_Pervasives_Native.Some _30067)
                  uu____30064
                 in
              FStar_Syntax_Syntax.new_bv uu____30061 t1  in
            let uu____30068 =
              let uu____30073 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30073
               in
            match uu____30068 with | (p,wl1) -> (p, x, wl1)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * lstring) ->
         (FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        (let uu____30131 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____30131
         then
           let uu____30136 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____30136
         else ());
        (let uu____30143 =
           FStar_Util.record_time (fun uu____30150  -> solve env probs)  in
         match uu____30143 with
         | (sol,ms) ->
             ((let uu____30162 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____30162
               then
                 let uu____30167 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30167
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____30180 =
                     FStar_Util.record_time
                       (fun uu____30187  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____30180 with
                    | ((),ms1) ->
                        ((let uu____30198 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____30198
                          then
                            let uu____30203 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30203
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____30215 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____30215
                     then
                       let uu____30222 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30222
                     else ());
                    (let result = err (d, s)  in
                     FStar_Syntax_Unionfind.rollback tx; result)))))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____30248 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____30248
            then
              let uu____30253 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30253
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____30261 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____30261
             then
               let uu____30266 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30266
             else ());
            (let f2 =
               let uu____30272 =
                 let uu____30273 = FStar_Syntax_Util.unmeta f1  in
                 uu____30273.FStar_Syntax_Syntax.n  in
               match uu____30272 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30277 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3955_30278 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3955_30278.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3955_30278.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3955_30278.FStar_TypeChecker_Common.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred *
        FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____30321 =
              let uu____30322 =
                let uu____30323 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _30324  ->
                       FStar_TypeChecker_Common.NonTrivial _30324)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30323;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____30322  in
            FStar_All.pipe_left
              (fun _30331  -> FStar_Pervasives_Native.Some _30331)
              uu____30321
  
let with_guard_no_simp :
  'Auu____30341 .
    'Auu____30341 ->
      FStar_TypeChecker_Common.prob ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option
          -> FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____30381 =
              let uu____30382 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _30383  -> FStar_TypeChecker_Common.NonTrivial _30383)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30382;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30381
  
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____30416 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30416
           then
             let uu____30421 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30423 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30421
               uu____30423
           else ());
          (let uu____30428 =
             let uu____30433 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30433
              in
           match uu____30428 with
           | (prob,wl) ->
               let g =
                 let uu____30441 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30449  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30441  in
               ((let uu____30467 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30467
                 then
                   let uu____30472 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30472
                 else ());
                g))
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____30493 = try_teq true env t1 t2  in
        match uu____30493 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30498 = FStar_TypeChecker_Env.get_range env  in
              let uu____30499 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30498 uu____30499);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30507 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30507
              then
                let uu____30512 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30514 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30516 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30512
                  uu____30514 uu____30516
              else ());
             g)
  
let (get_teq_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____30540 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30540
         then
           let uu____30545 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30547 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30545
             uu____30547
         else ());
        (let uu____30552 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30552 with
         | (prob,x,wl) ->
             let g =
               let uu____30567 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30576  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30567  in
             ((let uu____30594 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30594
               then
                 let uu____30599 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30599
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30607 =
                     let uu____30608 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30608 g1  in
                   FStar_Pervasives_Native.Some uu____30607)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30630 = FStar_TypeChecker_Env.get_range env  in
          let uu____30631 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30630 uu____30631
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let rel =
          if env.FStar_TypeChecker_Env.use_eq
          then FStar_TypeChecker_Common.EQ
          else FStar_TypeChecker_Common.SUB  in
        (let uu____30660 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30660
         then
           let uu____30665 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30667 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30665 uu____30667
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30678 =
           let uu____30685 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30685 "sub_comp"
            in
         match uu____30678 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30698 =
                 FStar_Util.record_time
                   (fun uu____30710  ->
                      let uu____30711 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30720  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30711)
                  in
               match uu____30698 with
               | (r,ms) ->
                   ((let uu____30748 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30748
                     then
                       let uu____30753 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30755 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30757 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30753 uu____30755
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30757
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
      fun uu____30795  ->
        match uu____30795 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30838 =
                 let uu____30844 =
                   let uu____30846 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30848 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30846 uu____30848
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30844)  in
               let uu____30852 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30838 uu____30852)
               in
            let equiv1 v1 v' =
              let uu____30865 =
                let uu____30870 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30871 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30870, uu____30871)  in
              match uu____30865 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30891 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____30922 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30922 with
                      | FStar_Syntax_Syntax.U_unif uu____30929 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30958  ->
                                    match uu____30958 with
                                    | (u,v') ->
                                        let uu____30967 = equiv1 v1 v'  in
                                        if uu____30967
                                        then
                                          let uu____30972 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30972 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____30993 -> []))
               in
            let uu____30998 =
              let wl =
                let uu___4066_31002 = empty_worklist env  in
                {
                  attempting = (uu___4066_31002.attempting);
                  wl_deferred = (uu___4066_31002.wl_deferred);
                  ctr = (uu___4066_31002.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4066_31002.smt_ok);
                  umax_heuristic_ok = (uu___4066_31002.umax_heuristic_ok);
                  tcenv = (uu___4066_31002.tcenv);
                  wl_implicits = (uu___4066_31002.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31021  ->
                      match uu____31021 with
                      | (lb,v1) ->
                          let uu____31028 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____31028 with
                           | USolved wl1 -> ()
                           | uu____31031 -> fail1 lb v1)))
               in
            let rec check_ineq uu____31042 =
              match uu____31042 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____31054) -> true
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
                      uu____31078,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____31080,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____31091) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____31099,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____31108 -> false)
               in
            let uu____31114 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31131  ->
                      match uu____31131 with
                      | (u,v1) ->
                          let uu____31139 = check_ineq (u, v1)  in
                          if uu____31139
                          then true
                          else
                            ((let uu____31147 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____31147
                              then
                                let uu____31152 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____31154 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____31152
                                  uu____31154
                              else ());
                             false)))
               in
            if uu____31114
            then ()
            else
              ((let uu____31164 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____31164
                then
                  ((let uu____31170 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31170);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31182 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31182))
                else ());
               (let uu____31195 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31195))
  
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
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun defer_ok  ->
    fun env  ->
      fun g  ->
        let fail1 uu____31268 =
          match uu____31268 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4143_31291 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4143_31291.attempting);
            wl_deferred = (uu___4143_31291.wl_deferred);
            ctr = (uu___4143_31291.ctr);
            defer_ok;
            smt_ok = (uu___4143_31291.smt_ok);
            umax_heuristic_ok = (uu___4143_31291.umax_heuristic_ok);
            tcenv = (uu___4143_31291.tcenv);
            wl_implicits = (uu___4143_31291.wl_implicits)
          }  in
        (let uu____31294 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31294
         then
           let uu____31299 = FStar_Util.string_of_bool defer_ok  in
           let uu____31301 = wl_to_string wl  in
           let uu____31303 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____31299 uu____31301 uu____31303
         else ());
        (let g1 =
           let uu____31309 = solve_and_commit env wl fail1  in
           match uu____31309 with
           | FStar_Pervasives_Native.Some
               (uu____31316::uu____31317,uu____31318) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4158_31347 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4158_31347.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4158_31347.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____31348 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4163_31357 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4163_31357.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4163_31357.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4163_31357.FStar_TypeChecker_Common.implicits)
          }))
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints false env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true env g 
let (discharge_guard' :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
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
            let uu___4175_31434 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4175_31434.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4175_31434.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4175_31434.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____31435 =
            let uu____31437 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____31437  in
          if uu____31435
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____31449 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____31450 =
                       let uu____31452 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____31452
                        in
                     FStar_Errors.diag uu____31449 uu____31450)
                  else ();
                  (let vc1 =
                     let uu____31458 =
                       let uu____31462 =
                         let uu____31464 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____31464  in
                       FStar_Pervasives_Native.Some uu____31462  in
                     FStar_Profiling.profile
                       (fun uu____31467  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____31458 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug1
                   then
                     (let uu____31471 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31472 =
                        let uu____31474 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31474
                         in
                      FStar_Errors.diag uu____31471 uu____31472)
                   else ();
                   (let uu____31480 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31480
                      "discharge_guard'" env vc1);
                   (let uu____31482 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31482 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____31491 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31492 =
                                let uu____31494 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31494
                                 in
                              FStar_Errors.diag uu____31491 uu____31492)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____31504 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31505 =
                                let uu____31507 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31507
                                 in
                              FStar_Errors.diag uu____31504 uu____31505)
                           else ();
                           (let vcs =
                              let uu____31521 = FStar_Options.use_tactics ()
                                 in
                              if uu____31521
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31543  ->
                                     (let uu____31545 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____31545);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31589  ->
                                              match uu____31589 with
                                              | (env1,goal,opts) ->
                                                  let uu____31605 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31605, opts)))))
                              else
                                (let uu____31609 =
                                   let uu____31616 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31616)  in
                                 [uu____31609])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31649  ->
                                    match uu____31649 with
                                    | (env1,goal,opts) ->
                                        let uu____31659 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31659 with
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
                                              if debug1
                                              then
                                                (let uu____31670 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31671 =
                                                   let uu____31673 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31675 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31673 uu____31675
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31670 uu____31671)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____31682 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31683 =
                                                   let uu____31685 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31685
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31682 uu____31683)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal1;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31703 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31703 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31712 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31712
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31726 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31726 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31756 = try_teq false env t1 t2  in
        match uu____31756 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
  
let (resolve_implicits' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun must_total  ->
      fun forcelax  ->
        fun g  ->
          let rec unresolved ctx_u =
            let uu____31800 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31800 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31813 ->
                     let uu____31826 =
                       let uu____31827 = FStar_Syntax_Subst.compress r  in
                       uu____31827.FStar_Syntax_Syntax.n  in
                     (match uu____31826 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31832) ->
                          unresolved ctx_u'
                      | uu____31849 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31873 = acc  in
            match uu____31873 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____31892 = hd1  in
                     (match uu____31892 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____31903 = unresolved ctx_u  in
                             if uu____31903
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31927 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31927
                                     then
                                       let uu____31931 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31931
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31940 = teq_nosmt env1 t tm
                                          in
                                       match uu____31940 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4288_31950 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4288_31950.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4288_31950.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4288_31950.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4288_31950.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4288_31950.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4288_31950.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4288_31950.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4291_31958 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4291_31958.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4291_31958.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4291_31958.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl1)))
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4295_31969 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4295_31969.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4295_31969.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4295_31969.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4295_31969.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4295_31969.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4295_31969.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4295_31969.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4295_31969.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4295_31969.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4295_31969.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4295_31969.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4295_31969.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4295_31969.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4295_31969.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4295_31969.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4295_31969.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4295_31969.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4295_31969.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4295_31969.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4295_31969.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4295_31969.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4295_31969.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4295_31969.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4295_31969.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4295_31969.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4295_31969.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4295_31969.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4295_31969.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4295_31969.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4295_31969.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4295_31969.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4295_31969.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4295_31969.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4295_31969.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4295_31969.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4295_31969.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4295_31969.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4295_31969.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4295_31969.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4295_31969.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4295_31969.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4295_31969.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4295_31969.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4295_31969.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4295_31969.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4295_31969.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4300_31974 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4300_31974.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4300_31974.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4300_31974.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4300_31974.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4300_31974.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4300_31974.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4300_31974.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4300_31974.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4300_31974.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4300_31974.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4300_31974.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4300_31974.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4300_31974.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4300_31974.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4300_31974.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4300_31974.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4300_31974.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4300_31974.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4300_31974.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4300_31974.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4300_31974.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4300_31974.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4300_31974.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4300_31974.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4300_31974.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4300_31974.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4300_31974.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4300_31974.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4300_31974.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4300_31974.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4300_31974.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4300_31974.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4300_31974.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4300_31974.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4300_31974.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4300_31974.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4300_31974.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4300_31974.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4300_31974.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4300_31974.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4300_31974.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4300_31974.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4300_31974.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4300_31974.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4300_31974.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4300_31974.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31979 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31979
                                   then
                                     let uu____31984 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31986 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31988 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31990 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31984 uu____31986 uu____31988
                                       reason uu____31990
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4306_31997  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____32004 =
                                             let uu____32014 =
                                               let uu____32022 =
                                                 let uu____32024 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____32026 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____32028 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____32024 uu____32026
                                                   uu____32028
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____32022, r)
                                                in
                                             [uu____32014]  in
                                           FStar_Errors.add_errors
                                             uu____32004);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____32047 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____32058  ->
                                               let uu____32059 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____32061 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____32063 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____32059 uu____32061
                                                 reason uu____32063)) env2 g1
                                         true
                                        in
                                     match uu____32047 with
                                     | FStar_Pervasives_Native.Some g2 -> g2
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Common.implicits
                                         out), true) tl1)))))
             in
          let uu___4318_32071 = g  in
          let uu____32072 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4318_32071.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4318_32071.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4318_32071.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____32072
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      resolve_implicits' env
        ((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
           (Prims.op_Negation env.FStar_TypeChecker_Env.lax)) false g
  
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.guard_t -> unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____32112 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____32112 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____32113 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____32113
      | imp::uu____32115 ->
          let uu____32118 =
            let uu____32124 =
              let uu____32126 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____32128 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____32126 uu____32128
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____32124)
             in
          FStar_Errors.raise_error uu____32118
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32148 = teq env t1 t2  in
        force_trivial_guard env uu____32148
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32167 = teq_nosmt env t1 t2  in
        match uu____32167 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4343_32186 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4343_32186.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4343_32186.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4343_32186.FStar_TypeChecker_Common.implicits)
      }
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Common.guard_t)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32222 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32222
         then
           let uu____32227 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32229 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____32227
             uu____32229
         else ());
        (let uu____32234 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32234 with
         | (prob,x,wl) ->
             let g =
               let uu____32253 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____32262  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32253  in
             ((let uu____32280 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____32280
               then
                 let uu____32285 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____32287 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____32289 =
                   let uu____32291 = FStar_Util.must g  in
                   guard_to_string env uu____32291  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____32285 uu____32287 uu____32289
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
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32328 = check_subtyping env t1 t2  in
        match uu____32328 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32347 =
              let uu____32348 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____32348 g  in
            FStar_Pervasives_Native.Some uu____32347
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32367 = check_subtyping env t1 t2  in
        match uu____32367 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32386 =
              let uu____32387 =
                let uu____32388 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____32388]  in
              FStar_TypeChecker_Env.close_guard env uu____32387 g  in
            FStar_Pervasives_Native.Some uu____32386
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32426 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32426
         then
           let uu____32431 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32433 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32431
             uu____32433
         else ());
        (let uu____32438 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32438 with
         | (prob,x,wl) ->
             let g =
               let uu____32453 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32462  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32453  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32483 =
                      let uu____32484 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32484]  in
                    FStar_TypeChecker_Env.close_guard env uu____32483 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32525 = subtype_nosmt env t1 t2  in
        match uu____32525 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  