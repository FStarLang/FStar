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
                    let uu____541 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____541;
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
                   (let uu____573 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace")
                       in
                    if uu____573
                    then
                      let uu____577 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                         in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____577
                    else ());
                   (ctx_uvar, t,
                     ((let uu___73_583 = wl  in
                       {
                         attempting = (uu___73_583.attempting);
                         wl_deferred = (uu___73_583.wl_deferred);
                         ctr = (uu___73_583.ctr);
                         defer_ok = (uu___73_583.defer_ok);
                         smt_ok = (uu___73_583.smt_ok);
                         umax_heuristic_ok = (uu___73_583.umax_heuristic_ok);
                         tcenv = (uu___73_583.tcenv);
                         wl_implicits = (imp :: (wl.wl_implicits))
                       }))))
  
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
            let uu___79_616 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___79_616.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___79_616.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___79_616.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___79_616.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___79_616.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___79_616.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___79_616.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___79_616.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___79_616.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___79_616.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___79_616.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___79_616.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___79_616.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___79_616.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___79_616.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___79_616.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___79_616.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___79_616.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___79_616.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___79_616.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___79_616.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___79_616.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___79_616.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___79_616.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___79_616.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___79_616.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___79_616.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___79_616.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___79_616.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___79_616.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___79_616.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___79_616.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___79_616.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___79_616.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___79_616.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___79_616.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___79_616.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___79_616.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___79_616.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___79_616.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___79_616.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___79_616.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___79_616.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___79_616.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___79_616.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___79_616.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____618 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____618 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____705 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____740 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____770 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____781 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____792 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_810  ->
    match uu___0_810 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____822 = FStar_Syntax_Util.head_and_args t  in
    match uu____822 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____885 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____887 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____902 =
                     let uu____904 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____904  in
                   FStar_Util.format1 "@<%s>" uu____902
                in
             let uu____908 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____885 uu____887 uu____908
         | uu____911 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_923  ->
      match uu___1_923 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____928 =
            let uu____932 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____934 =
              let uu____938 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____940 =
                let uu____944 =
                  let uu____948 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____948]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____944
                 in
              uu____938 :: uu____940  in
            uu____932 :: uu____934  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____928
      | FStar_TypeChecker_Common.CProb p ->
          let uu____959 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____961 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____963 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____959 uu____961
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____963
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_977  ->
      match uu___2_977 with
      | UNIV (u,t) ->
          let x =
            let uu____983 = FStar_Options.hide_uvar_nums ()  in
            if uu____983
            then "?"
            else
              (let uu____990 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____990 FStar_Util.string_of_int)
             in
          let uu____994 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____994
      | TERM (u,t) ->
          let x =
            let uu____1001 = FStar_Options.hide_uvar_nums ()  in
            if uu____1001
            then "?"
            else
              (let uu____1008 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1008 FStar_Util.string_of_int)
             in
          let uu____1012 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1012
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1031 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1031 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1052 =
      let uu____1056 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1056
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1052 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1075 .
    (FStar_Syntax_Syntax.term * 'Auu____1075) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1094 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1115  ->
              match uu____1115 with
              | (x,uu____1122) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1094 (FStar_String.concat " ")
  
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
        (let uu____1162 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1162
         then
           let uu____1167 = FStar_Thunk.force reason  in
           let uu____1170 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1167 uu____1170
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1193 = FStar_Thunk.mk (fun uu____1196  -> reason)  in
        giveup env uu____1193 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1202  ->
    match uu___3_1202 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1208 .
    'Auu____1208 FStar_TypeChecker_Common.problem ->
      'Auu____1208 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___143_1220 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___143_1220.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___143_1220.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___143_1220.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___143_1220.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___143_1220.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___143_1220.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___143_1220.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1228 .
    'Auu____1228 FStar_TypeChecker_Common.problem ->
      'Auu____1228 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1248  ->
    match uu___4_1248 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1254  -> FStar_TypeChecker_Common.TProb _1254)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1260  -> FStar_TypeChecker_Common.CProb _1260)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1266  ->
    match uu___5_1266 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___155_1272 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___155_1272.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___155_1272.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___155_1272.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___155_1272.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___155_1272.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___155_1272.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___155_1272.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___155_1272.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___155_1272.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___159_1280 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___159_1280.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___159_1280.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___159_1280.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___159_1280.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___159_1280.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___159_1280.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___159_1280.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___159_1280.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___159_1280.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1293  ->
      match uu___6_1293 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1300  ->
    match uu___7_1300 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1313  ->
    match uu___8_1313 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1328  ->
    match uu___9_1328 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1343  ->
    match uu___10_1343 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1357  ->
    match uu___11_1357 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1371  ->
    match uu___12_1371 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1383  ->
    match uu___13_1383 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1399 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1399) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1429 =
          let uu____1431 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1431  in
        if uu____1429
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1468)::bs ->
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
          let uu____1515 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1539 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1539]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1515
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1567 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1591 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1591]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1567
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1638 =
          let uu____1640 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1640  in
        if uu____1638
        then ()
        else
          (let uu____1645 =
             let uu____1648 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1648
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1645 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1697 =
          let uu____1699 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1699  in
        if uu____1697
        then ()
        else
          (let uu____1704 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1704)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1724 =
        let uu____1726 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1726  in
      if uu____1724
      then ()
      else
        (let msgf m =
           let uu____1740 =
             let uu____1742 =
               let uu____1744 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____1744 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____1742  in
           Prims.op_Hat msg uu____1740  in
         (let uu____1749 = msgf "scope"  in
          let uu____1752 = p_scope prob  in
          def_scope_wf uu____1749 (p_loc prob) uu____1752);
         (let uu____1764 = msgf "guard"  in
          def_check_scoped uu____1764 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1771 = msgf "lhs"  in
                def_check_scoped uu____1771 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1774 = msgf "rhs"  in
                def_check_scoped uu____1774 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1781 = msgf "lhs"  in
                def_check_scoped_comp uu____1781 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1784 = msgf "rhs"  in
                def_check_scoped_comp uu____1784 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___252_1805 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___252_1805.wl_deferred);
          ctr = (uu___252_1805.ctr);
          defer_ok = (uu___252_1805.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___252_1805.umax_heuristic_ok);
          tcenv = (uu___252_1805.tcenv);
          wl_implicits = (uu___252_1805.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1813 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1813 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___256_1836 = empty_worklist env  in
      let uu____1837 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1837;
        wl_deferred = (uu___256_1836.wl_deferred);
        ctr = (uu___256_1836.ctr);
        defer_ok = (uu___256_1836.defer_ok);
        smt_ok = (uu___256_1836.smt_ok);
        umax_heuristic_ok = (uu___256_1836.umax_heuristic_ok);
        tcenv = (uu___256_1836.tcenv);
        wl_implicits = (uu___256_1836.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___261_1858 = wl  in
        {
          attempting = (uu___261_1858.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___261_1858.ctr);
          defer_ok = (uu___261_1858.defer_ok);
          smt_ok = (uu___261_1858.smt_ok);
          umax_heuristic_ok = (uu___261_1858.umax_heuristic_ok);
          tcenv = (uu___261_1858.tcenv);
          wl_implicits = (uu___261_1858.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____1885 = FStar_Thunk.mkv reason  in defer uu____1885 prob wl
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___269_1904 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___269_1904.wl_deferred);
         ctr = (uu___269_1904.ctr);
         defer_ok = (uu___269_1904.defer_ok);
         smt_ok = (uu___269_1904.smt_ok);
         umax_heuristic_ok = (uu___269_1904.umax_heuristic_ok);
         tcenv = (uu___269_1904.tcenv);
         wl_implicits = (uu___269_1904.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1918 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1918 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____1952 = FStar_Syntax_Util.type_u ()  in
            match uu____1952 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____1964 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____1964 with
                 | (uu____1982,tt,wl1) ->
                     let uu____1985 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____1985, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_1991  ->
    match uu___14_1991 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _1997  -> FStar_TypeChecker_Common.TProb _1997) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _2003  -> FStar_TypeChecker_Common.CProb _2003) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2011 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2011 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2031  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2073 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2073 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2073 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2073 FStar_TypeChecker_Common.problem *
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
                        let uu____2160 =
                          let uu____2169 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2169]  in
                        FStar_List.append scope uu____2160
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2212 =
                      let uu____2215 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2215  in
                    FStar_List.append uu____2212
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2234 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2234 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2260 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2260;
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
                  (let uu____2334 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2334 with
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
                  (let uu____2422 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2422 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2460 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2460 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2460 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2460 FStar_TypeChecker_Common.problem *
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
                          let uu____2528 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2528]  in
                        let uu____2547 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2547
                     in
                  let uu____2550 =
                    let uu____2557 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___352_2568 = wl  in
                       {
                         attempting = (uu___352_2568.attempting);
                         wl_deferred = (uu___352_2568.wl_deferred);
                         ctr = (uu___352_2568.ctr);
                         defer_ok = (uu___352_2568.defer_ok);
                         smt_ok = (uu___352_2568.smt_ok);
                         umax_heuristic_ok =
                           (uu___352_2568.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___352_2568.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2557
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2550 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2586 =
                              let uu____2591 =
                                let uu____2592 =
                                  let uu____2601 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2601
                                   in
                                [uu____2592]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2591  in
                            uu____2586 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2629 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2629;
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
                let uu____2677 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2677;
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
  'Auu____2692 .
    worklist ->
      'Auu____2692 FStar_TypeChecker_Common.problem ->
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
              let uu____2725 =
                let uu____2728 =
                  let uu____2729 =
                    let uu____2736 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2736)  in
                  FStar_Syntax_Syntax.NT uu____2729  in
                [uu____2728]  in
              FStar_Syntax_Subst.subst uu____2725 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2758 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2758
        then
          let uu____2766 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2769 = prob_to_string env d  in
          let uu____2771 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____2778 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2766 uu____2769 uu____2771 uu____2778
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2790 -> failwith "impossible"  in
           let uu____2793 =
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
           match uu____2793 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2836  ->
            match uu___15_2836 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2848 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2852 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2852 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2883  ->
           match uu___16_2883 with
           | UNIV uu____2886 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2893 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2893
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
        (fun uu___17_2921  ->
           match uu___17_2921 with
           | UNIV (u',t) ->
               let uu____2926 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2926
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2933 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2945 =
        let uu____2946 =
          let uu____2947 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2947
           in
        FStar_Syntax_Subst.compress uu____2946  in
      FStar_All.pipe_right uu____2945 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2959 =
        let uu____2960 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____2960  in
      FStar_All.pipe_right uu____2959 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2972 =
        let uu____2976 =
          let uu____2978 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____2978  in
        FStar_Pervasives_Native.Some uu____2976  in
      FStar_Profiling.profile (fun uu____2981  -> sn' env t) uu____2972
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
          let uu____3006 =
            let uu____3010 =
              let uu____3012 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3012  in
            FStar_Pervasives_Native.Some uu____3010  in
          FStar_Profiling.profile
            (fun uu____3015  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3006
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3023 = FStar_Syntax_Util.head_and_args t  in
    match uu____3023 with
    | (h,uu____3042) ->
        let uu____3067 =
          let uu____3068 = FStar_Syntax_Subst.compress h  in
          uu____3068.FStar_Syntax_Syntax.n  in
        (match uu____3067 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3073 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3086 =
        let uu____3090 =
          let uu____3092 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3092  in
        FStar_Pervasives_Native.Some uu____3090  in
      FStar_Profiling.profile
        (fun uu____3097  ->
           let uu____3098 = should_strongly_reduce t  in
           if uu____3098
           then
             let uu____3101 =
               let uu____3102 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3102  in
             FStar_All.pipe_right uu____3101 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3086 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'Auu____3113 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3113) ->
        (FStar_Syntax_Syntax.term * 'Auu____3113)
  =
  fun env  ->
    fun t  ->
      let uu____3136 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3136, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3188  ->
              match uu____3188 with
              | (x,imp) ->
                  let uu____3207 =
                    let uu___458_3208 = x  in
                    let uu____3209 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___458_3208.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___458_3208.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3209
                    }  in
                  (uu____3207, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3233 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3233
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3237 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3237
        | uu____3240 -> u2  in
      let uu____3241 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3241
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3258 =
          let uu____3262 =
            let uu____3264 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3264  in
          FStar_Pervasives_Native.Some uu____3262  in
        FStar_Profiling.profile
          (fun uu____3267  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3258 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
                (let uu____3389 = norm_refinement env t12  in
                 match uu____3389 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3404;
                     FStar_Syntax_Syntax.vars = uu____3405;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3429 =
                       let uu____3431 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3433 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3431 uu____3433
                        in
                     failwith uu____3429)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3449 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3449
          | FStar_Syntax_Syntax.Tm_uinst uu____3450 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3487 =
                   let uu____3488 = FStar_Syntax_Subst.compress t1'  in
                   uu____3488.FStar_Syntax_Syntax.n  in
                 match uu____3487 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3503 -> aux true t1'
                 | uu____3511 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3526 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3557 =
                   let uu____3558 = FStar_Syntax_Subst.compress t1'  in
                   uu____3558.FStar_Syntax_Syntax.n  in
                 match uu____3557 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3573 -> aux true t1'
                 | uu____3581 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3596 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3643 =
                   let uu____3644 = FStar_Syntax_Subst.compress t1'  in
                   uu____3644.FStar_Syntax_Syntax.n  in
                 match uu____3643 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3659 -> aux true t1'
                 | uu____3667 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3682 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3697 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3712 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3727 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3742 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3771 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3804 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3825 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3852 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3880 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3917 ->
              let uu____3924 =
                let uu____3926 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3928 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3926 uu____3928
                 in
              failwith uu____3924
          | FStar_Syntax_Syntax.Tm_ascribed uu____3943 ->
              let uu____3970 =
                let uu____3972 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3974 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3972 uu____3974
                 in
              failwith uu____3970
          | FStar_Syntax_Syntax.Tm_delayed uu____3989 ->
              let uu____4004 =
                let uu____4006 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4008 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4006 uu____4008
                 in
              failwith uu____4004
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4023 =
                let uu____4025 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4027 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4025 uu____4027
                 in
              failwith uu____4023
           in
        let uu____4042 = whnf env t1  in aux false uu____4042
  
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
      let uu____4087 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4087 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4128 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4128, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4155 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4155 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4215  ->
    match uu____4215 with
    | (t_base,refopt) ->
        let uu____4246 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4246 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4288 =
      let uu____4292 =
        let uu____4295 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4320  ->
                  match uu____4320 with | (uu____4328,uu____4329,x) -> x))
           in
        FStar_List.append wl.attempting uu____4295  in
      FStar_List.map (wl_prob_to_string wl) uu____4292  in
    FStar_All.pipe_right uu____4288 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____4350 .
    ('Auu____4350 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4362  ->
    match uu____4362 with
    | (uu____4369,c,args) ->
        let uu____4372 = print_ctx_uvar c  in
        let uu____4374 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4372 uu____4374
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4384 = FStar_Syntax_Util.head_and_args t  in
    match uu____4384 with
    | (head1,_args) ->
        let uu____4428 =
          let uu____4429 = FStar_Syntax_Subst.compress head1  in
          uu____4429.FStar_Syntax_Syntax.n  in
        (match uu____4428 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4433 -> true
         | uu____4447 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4455 = FStar_Syntax_Util.head_and_args t  in
    match uu____4455 with
    | (head1,_args) ->
        let uu____4498 =
          let uu____4499 = FStar_Syntax_Subst.compress head1  in
          uu____4499.FStar_Syntax_Syntax.n  in
        (match uu____4498 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4503) -> u
         | uu____4520 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4545 = FStar_Syntax_Util.head_and_args t  in
      match uu____4545 with
      | (head1,args) ->
          let uu____4592 =
            let uu____4593 = FStar_Syntax_Subst.compress head1  in
            uu____4593.FStar_Syntax_Syntax.n  in
          (match uu____4592 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4601)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4634 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_4659  ->
                         match uu___18_4659 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4664 =
                               let uu____4665 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4665.FStar_Syntax_Syntax.n  in
                             (match uu____4664 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4670 -> false)
                         | uu____4672 -> true))
                  in
               (match uu____4634 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4697 =
                        FStar_List.collect
                          (fun uu___19_4709  ->
                             match uu___19_4709 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4713 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4713]
                             | uu____4714 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4697 FStar_List.rev  in
                    let uu____4737 =
                      let uu____4744 =
                        let uu____4753 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_4775  ->
                                  match uu___20_4775 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4779 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4779]
                                  | uu____4780 -> []))
                           in
                        FStar_All.pipe_right uu____4753 FStar_List.rev  in
                      let uu____4803 =
                        let uu____4806 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4806  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4744 uu____4803
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____4737 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4842  ->
                                match uu____4842 with
                                | (x,i) ->
                                    let uu____4861 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4861, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4892  ->
                                match uu____4892 with
                                | (a,i) ->
                                    let uu____4911 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4911, i)) args_sol
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
           | uu____4933 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4955 =
          let uu____4978 =
            let uu____4979 = FStar_Syntax_Subst.compress k  in
            uu____4979.FStar_Syntax_Syntax.n  in
          match uu____4978 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5061 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5061)
              else
                (let uu____5096 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5096 with
                 | (ys',t1,uu____5129) ->
                     let uu____5134 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5134))
          | uu____5173 ->
              let uu____5174 =
                let uu____5179 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5179)  in
              ((ys, t), uu____5174)
           in
        match uu____4955 with
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
                 let uu____5274 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5274 c  in
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
               (let uu____5352 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5352
                then
                  let uu____5357 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5359 = print_ctx_uvar uv  in
                  let uu____5361 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5357 uu____5359 uu____5361
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5370 =
                   let uu____5372 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5372  in
                 let uu____5375 =
                   let uu____5378 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5378
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5370 uu____5375 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5411 =
               let uu____5412 =
                 let uu____5414 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5416 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5414 uu____5416
                  in
               failwith uu____5412  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5482  ->
                       match uu____5482 with
                       | (a,i) ->
                           let uu____5503 =
                             let uu____5504 = FStar_Syntax_Subst.compress a
                                in
                             uu____5504.FStar_Syntax_Syntax.n  in
                           (match uu____5503 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5530 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5540 =
                 let uu____5542 = is_flex g  in Prims.op_Negation uu____5542
                  in
               if uu____5540
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5551 = destruct_flex_t g wl  in
                  match uu____5551 with
                  | ((uu____5556,uv1,args),wl1) ->
                      ((let uu____5561 = args_as_binders args  in
                        assign_solution uu____5561 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___711_5563 = wl1  in
              {
                attempting = (uu___711_5563.attempting);
                wl_deferred = (uu___711_5563.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___711_5563.defer_ok);
                smt_ok = (uu___711_5563.smt_ok);
                umax_heuristic_ok = (uu___711_5563.umax_heuristic_ok);
                tcenv = (uu___711_5563.tcenv);
                wl_implicits = (uu___711_5563.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5588 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5588
         then
           let uu____5593 = FStar_Util.string_of_int pid  in
           let uu____5595 =
             let uu____5597 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5597 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5593 uu____5595
         else ());
        commit sol;
        (let uu___719_5611 = wl  in
         {
           attempting = (uu___719_5611.attempting);
           wl_deferred = (uu___719_5611.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___719_5611.defer_ok);
           smt_ok = (uu___719_5611.smt_ok);
           umax_heuristic_ok = (uu___719_5611.umax_heuristic_ok);
           tcenv = (uu___719_5611.tcenv);
           wl_implicits = (uu___719_5611.wl_implicits)
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
          (let uu____5647 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____5647
           then
             let uu____5652 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____5656 =
               let uu____5658 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____5658 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5652 uu____5656
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
        let uu____5693 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5693 FStar_Util.set_elements  in
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
      let uu____5733 = occurs uk t  in
      match uu____5733 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5772 =
                 let uu____5774 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5776 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5774 uu____5776
                  in
               FStar_Pervasives_Native.Some uu____5772)
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
            let uu____5896 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5896 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5947 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6004  ->
             match uu____6004 with
             | (x,uu____6016) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6034 = FStar_List.last bs  in
      match uu____6034 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6058) ->
          let uu____6069 =
            FStar_Util.prefix_until
              (fun uu___21_6084  ->
                 match uu___21_6084 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6087 -> false) g
             in
          (match uu____6069 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6101,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6138 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6138 with
        | (pfx,uu____6148) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6160 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6160 with
             | (uu____6168,src',wl1) ->
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
                 | uu____6282 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6283 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6347  ->
                  fun uu____6348  ->
                    match (uu____6347, uu____6348) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6451 =
                          let uu____6453 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6453
                           in
                        if uu____6451
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6487 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6487
                           then
                             let uu____6504 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6504)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6283 with | (isect,uu____6554) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6590 'Auu____6591 .
    (FStar_Syntax_Syntax.bv * 'Auu____6590) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6591) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6649  ->
              fun uu____6650  ->
                match (uu____6649, uu____6650) with
                | ((a,uu____6669),(b,uu____6671)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6687 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6687) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6718  ->
           match uu____6718 with
           | (y,uu____6725) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6735 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6735) Prims.list ->
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
                   let uu____6897 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6897
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6930 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6982 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7026 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7047 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7055  ->
    match uu___22_7055 with
    | MisMatch (d1,d2) ->
        let uu____7067 =
          let uu____7069 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7071 =
            let uu____7073 =
              let uu____7075 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7075 ")"  in
            Prims.op_Hat ") (" uu____7073  in
          Prims.op_Hat uu____7069 uu____7071  in
        Prims.op_Hat "MisMatch (" uu____7067
    | HeadMatch u ->
        let uu____7082 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7082
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7091  ->
    match uu___23_7091 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7108 -> HeadMatch false
  
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
          let uu____7130 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7130 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7141 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7165 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7175 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7194 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7194
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7195 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7196 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7197 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7210 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7224 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7248) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7254,uu____7255) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7297) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7322;
             FStar_Syntax_Syntax.index = uu____7323;
             FStar_Syntax_Syntax.sort = t2;_},uu____7325)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7333 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7334 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7335 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7350 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7357 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7377 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7377
  
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
           { FStar_Syntax_Syntax.blob = uu____7396;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7397;
             FStar_Syntax_Syntax.ltyp = uu____7398;
             FStar_Syntax_Syntax.rng = uu____7399;_},uu____7400)
            ->
            let uu____7411 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7411 t21
        | (uu____7412,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7413;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7414;
             FStar_Syntax_Syntax.ltyp = uu____7415;
             FStar_Syntax_Syntax.rng = uu____7416;_})
            ->
            let uu____7427 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7427
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7439 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7439
            then FullMatch
            else
              (let uu____7444 =
                 let uu____7453 =
                   let uu____7456 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7456  in
                 let uu____7457 =
                   let uu____7460 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7460  in
                 (uu____7453, uu____7457)  in
               MisMatch uu____7444)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7466),FStar_Syntax_Syntax.Tm_uinst (g,uu____7468)) ->
            let uu____7477 = head_matches env f g  in
            FStar_All.pipe_right uu____7477 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7478) -> HeadMatch true
        | (uu____7480,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7484 = FStar_Const.eq_const c d  in
            if uu____7484
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7494),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7496)) ->
            let uu____7529 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7529
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7539),FStar_Syntax_Syntax.Tm_refine (y,uu____7541)) ->
            let uu____7550 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7550 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7552),uu____7553) ->
            let uu____7558 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7558 head_match
        | (uu____7559,FStar_Syntax_Syntax.Tm_refine (x,uu____7561)) ->
            let uu____7566 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7566 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7567,FStar_Syntax_Syntax.Tm_type
           uu____7568) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7570,FStar_Syntax_Syntax.Tm_arrow uu____7571) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7602),FStar_Syntax_Syntax.Tm_app (head',uu____7604))
            ->
            let uu____7653 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7653 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7655),uu____7656) ->
            let uu____7681 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7681 head_match
        | (uu____7682,FStar_Syntax_Syntax.Tm_app (head1,uu____7684)) ->
            let uu____7709 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7709 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7710,FStar_Syntax_Syntax.Tm_let
           uu____7711) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7739,FStar_Syntax_Syntax.Tm_match uu____7740) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7786,FStar_Syntax_Syntax.Tm_abs
           uu____7787) -> HeadMatch true
        | uu____7825 ->
            let uu____7830 =
              let uu____7839 = delta_depth_of_term env t11  in
              let uu____7842 = delta_depth_of_term env t21  in
              (uu____7839, uu____7842)  in
            MisMatch uu____7830
  
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
              let uu____7911 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7911  in
            (let uu____7913 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7913
             then
               let uu____7918 = FStar_Syntax_Print.term_to_string t  in
               let uu____7920 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7918 uu____7920
             else ());
            (let uu____7925 =
               let uu____7926 = FStar_Syntax_Util.un_uinst head1  in
               uu____7926.FStar_Syntax_Syntax.n  in
             match uu____7925 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7932 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7932 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7946 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7946
                        then
                          let uu____7951 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7951
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7956 ->
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
                      let uu____7974 =
                        let uu____7976 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7976 = FStar_Syntax_Util.Equal  in
                      if uu____7974
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7983 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7983
                          then
                            let uu____7988 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____7990 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7988
                              uu____7990
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7995 -> FStar_Pervasives_Native.None)
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
            (let uu____8147 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8147
             then
               let uu____8152 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8154 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8156 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8152
                 uu____8154 uu____8156
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8184 =
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
               match uu____8184 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8232 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8232 with
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
                  uu____8270),uu____8271)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8292 =
                      let uu____8301 = maybe_inline t11  in
                      let uu____8304 = maybe_inline t21  in
                      (uu____8301, uu____8304)  in
                    match uu____8292 with
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
                 (uu____8347,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8348))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8369 =
                      let uu____8378 = maybe_inline t11  in
                      let uu____8381 = maybe_inline t21  in
                      (uu____8378, uu____8381)  in
                    match uu____8369 with
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
             | MisMatch uu____8436 -> fail1 n_delta r t11 t21
             | uu____8445 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8460 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8460
           then
             let uu____8465 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8467 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8469 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8477 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8494 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8494
                    (fun uu____8529  ->
                       match uu____8529 with
                       | (t11,t21) ->
                           let uu____8537 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8539 =
                             let uu____8541 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8541  in
                           Prims.op_Hat uu____8537 uu____8539))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8465 uu____8467 uu____8469 uu____8477
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8558 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8558 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8573  ->
    match uu___24_8573 with
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
      let uu___1208_8622 = p  in
      let uu____8625 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8626 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1208_8622.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8625;
        FStar_TypeChecker_Common.relation =
          (uu___1208_8622.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8626;
        FStar_TypeChecker_Common.element =
          (uu___1208_8622.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1208_8622.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1208_8622.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1208_8622.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1208_8622.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1208_8622.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8641 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8641
            (fun _8646  -> FStar_TypeChecker_Common.TProb _8646)
      | FStar_TypeChecker_Common.CProb uu____8647 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8670 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8670 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8678 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8678 with
           | (lh,lhs_args) ->
               let uu____8725 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8725 with
                | (rh,rhs_args) ->
                    let uu____8772 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8785,FStar_Syntax_Syntax.Tm_uvar uu____8786)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8875 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8902,uu____8903)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8918,FStar_Syntax_Syntax.Tm_uvar uu____8919)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8934,FStar_Syntax_Syntax.Tm_arrow uu____8935)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1259_8965 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1259_8965.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1259_8965.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1259_8965.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1259_8965.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1259_8965.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1259_8965.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1259_8965.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1259_8965.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1259_8965.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8968,FStar_Syntax_Syntax.Tm_type uu____8969)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1259_8985 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1259_8985.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1259_8985.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1259_8985.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1259_8985.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1259_8985.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1259_8985.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1259_8985.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1259_8985.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1259_8985.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8988,FStar_Syntax_Syntax.Tm_uvar uu____8989)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1259_9005 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1259_9005.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1259_9005.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1259_9005.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1259_9005.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1259_9005.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1259_9005.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1259_9005.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1259_9005.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1259_9005.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9008,FStar_Syntax_Syntax.Tm_uvar uu____9009)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9024,uu____9025)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9040,FStar_Syntax_Syntax.Tm_uvar uu____9041)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9056,uu____9057) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8772 with
                     | (rank,tp1) ->
                         let uu____9070 =
                           FStar_All.pipe_right
                             (let uu___1279_9074 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1279_9074.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1279_9074.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1279_9074.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1279_9074.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1279_9074.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1279_9074.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1279_9074.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1279_9074.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1279_9074.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9077  ->
                                FStar_TypeChecker_Common.TProb _9077)
                            in
                         (rank, uu____9070))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9081 =
            FStar_All.pipe_right
              (let uu___1283_9085 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1283_9085.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1283_9085.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1283_9085.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1283_9085.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1283_9085.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1283_9085.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1283_9085.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1283_9085.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1283_9085.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9088  -> FStar_TypeChecker_Common.CProb _9088)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9081)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9148 probs =
      match uu____9148 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9229 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9250 = rank wl.tcenv hd1  in
               (match uu____9250 with
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
                      (let uu____9311 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9316 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9316)
                          in
                       if uu____9311
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
          let uu____9389 = FStar_Syntax_Util.head_and_args t  in
          match uu____9389 with
          | (hd1,uu____9408) ->
              let uu____9433 =
                let uu____9434 = FStar_Syntax_Subst.compress hd1  in
                uu____9434.FStar_Syntax_Syntax.n  in
              (match uu____9433 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9439) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9474  ->
                           match uu____9474 with
                           | (y,uu____9483) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9506  ->
                                       match uu____9506 with
                                       | (x,uu____9515) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9520 -> false)
           in
        let uu____9522 = rank tcenv p  in
        match uu____9522 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9531 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9612 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9631 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9650 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9667 = FStar_Thunk.mkv s  in UFailed uu____9667 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9682 = FStar_Thunk.mk s  in UFailed uu____9682 
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
                        let uu____9734 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9734 with
                        | (k,uu____9742) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9755 -> false)))
            | uu____9757 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9809 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9817 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9817 = Prims.int_zero))
                           in
                        if uu____9809 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9838 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9846 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9846 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9838)
               in
            let uu____9850 = filter1 u12  in
            let uu____9853 = filter1 u22  in (uu____9850, uu____9853)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9888 = filter_out_common_univs us1 us2  in
                   (match uu____9888 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9948 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9948 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9951 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9968  ->
                               let uu____9969 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____9971 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9969 uu____9971))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9997 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9997 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10023 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10023 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10026 ->
                   ufailed_thunk
                     (fun uu____10037  ->
                        let uu____10038 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10040 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10038 uu____10040 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10043,uu____10044) ->
              let uu____10046 =
                let uu____10048 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10050 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10048 uu____10050
                 in
              failwith uu____10046
          | (FStar_Syntax_Syntax.U_unknown ,uu____10053) ->
              let uu____10054 =
                let uu____10056 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10058 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10056 uu____10058
                 in
              failwith uu____10054
          | (uu____10061,FStar_Syntax_Syntax.U_bvar uu____10062) ->
              let uu____10064 =
                let uu____10066 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10068 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10066 uu____10068
                 in
              failwith uu____10064
          | (uu____10071,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10072 =
                let uu____10074 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10076 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10074 uu____10076
                 in
              failwith uu____10072
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10106 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10106
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10123 = occurs_univ v1 u3  in
              if uu____10123
              then
                let uu____10126 =
                  let uu____10128 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10130 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10128 uu____10130
                   in
                try_umax_components u11 u21 uu____10126
              else
                (let uu____10135 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10135)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10147 = occurs_univ v1 u3  in
              if uu____10147
              then
                let uu____10150 =
                  let uu____10152 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10154 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10152 uu____10154
                   in
                try_umax_components u11 u21 uu____10150
              else
                (let uu____10159 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10159)
          | (FStar_Syntax_Syntax.U_max uu____10160,uu____10161) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10169 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10169
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10175,FStar_Syntax_Syntax.U_max uu____10176) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10184 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10184
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10190,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10192,FStar_Syntax_Syntax.U_name uu____10193) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10195) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10197) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10199,FStar_Syntax_Syntax.U_succ uu____10200) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10202,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10309 = bc1  in
      match uu____10309 with
      | (bs1,mk_cod1) ->
          let uu____10353 = bc2  in
          (match uu____10353 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10464 = aux xs ys  in
                     (match uu____10464 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10547 =
                       let uu____10554 = mk_cod1 xs  in ([], uu____10554)  in
                     let uu____10557 =
                       let uu____10564 = mk_cod2 ys  in ([], uu____10564)  in
                     (uu____10547, uu____10557)
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
                  let uu____10633 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10633 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10636 =
                    let uu____10637 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10637 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10636
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10642 = has_type_guard t1 t2  in (uu____10642, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10643 = has_type_guard t2 t1  in (uu____10643, wl)
  
let is_flex_pat :
  'Auu____10653 'Auu____10654 'Auu____10655 .
    ('Auu____10653 * 'Auu____10654 * 'Auu____10655 Prims.list) -> Prims.bool
  =
  fun uu___25_10669  ->
    match uu___25_10669 with
    | (uu____10678,uu____10679,[]) -> true
    | uu____10683 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10716 = f  in
      match uu____10716 with
      | (uu____10723,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10724;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10725;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10728;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10729;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10730;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10731;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10801  ->
                 match uu____10801 with
                 | (y,uu____10810) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10964 =
                  let uu____10979 =
                    let uu____10982 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10982  in
                  ((FStar_List.rev pat_binders), uu____10979)  in
                FStar_Pervasives_Native.Some uu____10964
            | (uu____11015,[]) ->
                let uu____11046 =
                  let uu____11061 =
                    let uu____11064 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11064  in
                  ((FStar_List.rev pat_binders), uu____11061)  in
                FStar_Pervasives_Native.Some uu____11046
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11155 =
                  let uu____11156 = FStar_Syntax_Subst.compress a  in
                  uu____11156.FStar_Syntax_Syntax.n  in
                (match uu____11155 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11176 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11176
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1611_11206 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1611_11206.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1611_11206.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11210 =
                            let uu____11211 =
                              let uu____11218 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11218)  in
                            FStar_Syntax_Syntax.NT uu____11211  in
                          [uu____11210]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1617_11234 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1617_11234.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1617_11234.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11235 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11275 =
                  let uu____11282 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11282  in
                (match uu____11275 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11341 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11366 ->
               let uu____11367 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11367 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11663 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11663
       then
         let uu____11668 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11668
       else ());
      (let uu____11674 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____11674
       then
         let uu____11679 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11679
       else ());
      (let uu____11684 = next_prob probs  in
       match uu____11684 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1644_11711 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1644_11711.wl_deferred);
               ctr = (uu___1644_11711.ctr);
               defer_ok = (uu___1644_11711.defer_ok);
               smt_ok = (uu___1644_11711.smt_ok);
               umax_heuristic_ok = (uu___1644_11711.umax_heuristic_ok);
               tcenv = (uu___1644_11711.tcenv);
               wl_implicits = (uu___1644_11711.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11720 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11720
                 then
                   let uu____11723 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11723
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
                       (let uu____11730 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd1
                            probs1
                           in
                        solve env uu____11730)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1656_11736 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1656_11736.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1656_11736.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1656_11736.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1656_11736.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1656_11736.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1656_11736.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1656_11736.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1656_11736.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1656_11736.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11761 ->
                let uu____11771 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11836  ->
                          match uu____11836 with
                          | (c,uu____11846,uu____11847) -> c < probs.ctr))
                   in
                (match uu____11771 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11895 =
                            let uu____11900 =
                              FStar_List.map
                                (fun uu____11921  ->
                                   match uu____11921 with
                                   | (uu____11937,x,y) ->
                                       let uu____11948 = FStar_Thunk.force x
                                          in
                                       (uu____11948, y)) probs.wl_deferred
                               in
                            (uu____11900, (probs.wl_implicits))  in
                          Success uu____11895
                      | uu____11952 ->
                          let uu____11962 =
                            let uu___1674_11963 = probs  in
                            let uu____11964 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11985  ->
                                      match uu____11985 with
                                      | (uu____11993,uu____11994,y) -> y))
                               in
                            {
                              attempting = uu____11964;
                              wl_deferred = rest;
                              ctr = (uu___1674_11963.ctr);
                              defer_ok = (uu___1674_11963.defer_ok);
                              smt_ok = (uu___1674_11963.smt_ok);
                              umax_heuristic_ok =
                                (uu___1674_11963.umax_heuristic_ok);
                              tcenv = (uu___1674_11963.tcenv);
                              wl_implicits = (uu___1674_11963.wl_implicits)
                            }  in
                          solve env uu____11962))))

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
            let uu____12003 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12003 with
            | USolved wl1 ->
                let uu____12005 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12005
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12008 = defer_lit "" orig wl1  in
                solve env uu____12008

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
                  let uu____12059 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12059 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12062 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12075;
                  FStar_Syntax_Syntax.vars = uu____12076;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12079;
                  FStar_Syntax_Syntax.vars = uu____12080;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12093,uu____12094) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12102,FStar_Syntax_Syntax.Tm_uinst uu____12103) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12111 -> USolved wl

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
            ((let uu____12122 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12122
              then
                let uu____12127 = prob_to_string env orig  in
                let uu____12129 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12127 uu____12129
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
               let uu____12222 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12222 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12277 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12277
                then
                  let uu____12282 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12284 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12282 uu____12284
                else ());
               (let uu____12289 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12289 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12335 = eq_prob t1 t2 wl2  in
                         (match uu____12335 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12356 ->
                         let uu____12365 = eq_prob t1 t2 wl2  in
                         (match uu____12365 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12415 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12430 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12431 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12430, uu____12431)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12436 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12437 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12436, uu____12437)
                            in
                         (match uu____12415 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12468 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12468 with
                                | (t1_hd,t1_args) ->
                                    let uu____12513 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12513 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12579 =
                                              let uu____12586 =
                                                let uu____12597 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12597 :: t1_args  in
                                              let uu____12614 =
                                                let uu____12623 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12623 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12672  ->
                                                   fun uu____12673  ->
                                                     fun uu____12674  ->
                                                       match (uu____12672,
                                                               uu____12673,
                                                               uu____12674)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12724),
                                                          (a2,uu____12726))
                                                           ->
                                                           let uu____12763 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12763
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12586
                                                uu____12614
                                               in
                                            match uu____12579 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1828_12789 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1828_12789.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1828_12789.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1828_12789.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12800 =
                                                  solve env1 wl'  in
                                                (match uu____12800 with
                                                 | Success (uu____12803,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1837_12807
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1837_12807.attempting);
                                                            wl_deferred =
                                                              (uu___1837_12807.wl_deferred);
                                                            ctr =
                                                              (uu___1837_12807.ctr);
                                                            defer_ok =
                                                              (uu___1837_12807.defer_ok);
                                                            smt_ok =
                                                              (uu___1837_12807.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1837_12807.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1837_12807.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12808 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12840 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12840 with
                                | (t1_base,p1_opt) ->
                                    let uu____12876 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12876 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____12975 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____12975
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
                                               let uu____13028 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13028
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
                                               let uu____13060 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13060
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
                                               let uu____13092 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13092
                                           | uu____13095 -> t_base  in
                                         let uu____13112 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13112 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13126 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13126, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13133 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13133 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13169 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13169 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13205 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13205
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
                              let uu____13229 = combine t11 t21 wl2  in
                              (match uu____13229 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13262 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13262
                                     then
                                       let uu____13267 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13267
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13309 ts1 =
               match uu____13309 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13372 = pairwise out t wl2  in
                        (match uu____13372 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13408 =
               let uu____13419 = FStar_List.hd ts  in (uu____13419, [], wl1)
                in
             let uu____13428 = FStar_List.tl ts  in
             aux uu____13408 uu____13428  in
           let uu____13435 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13435 with
           | (this_flex,this_rigid) ->
               let uu____13461 =
                 let uu____13462 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13462.FStar_Syntax_Syntax.n  in
               (match uu____13461 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13487 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13487
                    then
                      let uu____13490 = destruct_flex_t this_flex wl  in
                      (match uu____13490 with
                       | (flex,wl1) ->
                           let uu____13497 = quasi_pattern env flex  in
                           (match uu____13497 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13516 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13516
                                  then
                                    let uu____13521 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13521
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13528 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1939_13531 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1939_13531.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1939_13531.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1939_13531.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1939_13531.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1939_13531.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1939_13531.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1939_13531.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1939_13531.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1939_13531.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13528)
                | uu____13532 ->
                    ((let uu____13534 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13534
                      then
                        let uu____13539 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13539
                      else ());
                     (let uu____13544 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13544 with
                      | (u,_args) ->
                          let uu____13587 =
                            let uu____13588 = FStar_Syntax_Subst.compress u
                               in
                            uu____13588.FStar_Syntax_Syntax.n  in
                          (match uu____13587 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13616 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13616 with
                                 | (u',uu____13635) ->
                                     let uu____13660 =
                                       let uu____13661 = whnf env u'  in
                                       uu____13661.FStar_Syntax_Syntax.n  in
                                     (match uu____13660 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13683 -> false)
                                  in
                               let uu____13685 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13708  ->
                                         match uu___26_13708 with
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
                                              | uu____13722 -> false)
                                         | uu____13726 -> false))
                                  in
                               (match uu____13685 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13741 = whnf env this_rigid
                                         in
                                      let uu____13742 =
                                        FStar_List.collect
                                          (fun uu___27_13748  ->
                                             match uu___27_13748 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13754 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13754]
                                             | uu____13758 -> [])
                                          bounds_probs
                                         in
                                      uu____13741 :: uu____13742  in
                                    let uu____13759 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13759 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13792 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13807 =
                                               let uu____13808 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13808.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13807 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13820 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13820)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13831 -> bound  in
                                           let uu____13832 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13832)  in
                                         (match uu____13792 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13867 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13867
                                                then
                                                  let wl'1 =
                                                    let uu___1999_13873 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___1999_13873.wl_deferred);
                                                      ctr =
                                                        (uu___1999_13873.ctr);
                                                      defer_ok =
                                                        (uu___1999_13873.defer_ok);
                                                      smt_ok =
                                                        (uu___1999_13873.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___1999_13873.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___1999_13873.tcenv);
                                                      wl_implicits =
                                                        (uu___1999_13873.wl_implicits)
                                                    }  in
                                                  let uu____13874 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13874
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13880 =
                                                  solve_t env eq_prob
                                                    (let uu___2004_13882 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2004_13882.wl_deferred);
                                                       ctr =
                                                         (uu___2004_13882.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2004_13882.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2004_13882.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2004_13882.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13880 with
                                                | Success (uu____13884,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2010_13887 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2010_13887.wl_deferred);
                                                        ctr =
                                                          (uu___2010_13887.ctr);
                                                        defer_ok =
                                                          (uu___2010_13887.defer_ok);
                                                        smt_ok =
                                                          (uu___2010_13887.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2010_13887.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2010_13887.tcenv);
                                                        wl_implicits =
                                                          (uu___2010_13887.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2013_13889 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2013_13889.attempting);
                                                        wl_deferred =
                                                          (uu___2013_13889.wl_deferred);
                                                        ctr =
                                                          (uu___2013_13889.ctr);
                                                        defer_ok =
                                                          (uu___2013_13889.defer_ok);
                                                        smt_ok =
                                                          (uu___2013_13889.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2013_13889.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2013_13889.tcenv);
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
                                                    let uu____13905 =
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
                                                    ((let uu____13917 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13917
                                                      then
                                                        let uu____13922 =
                                                          let uu____13924 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13924
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13922
                                                      else ());
                                                     (let uu____13937 =
                                                        let uu____13952 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13952)
                                                         in
                                                      match uu____13937 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____13974))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14000 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14000
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
                                                                  let uu____14020
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14020))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14045 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14045
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
                                                                    let uu____14065
                                                                    =
                                                                    let uu____14070
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14070
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14065
                                                                    [] wl2
                                                                     in
                                                                  let uu____14076
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14076))))
                                                      | uu____14077 ->
                                                          let uu____14092 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14092 p)))))))
                           | uu____14099 when flip ->
                               let uu____14100 =
                                 let uu____14102 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14104 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14102 uu____14104
                                  in
                               failwith uu____14100
                           | uu____14107 ->
                               let uu____14108 =
                                 let uu____14110 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14112 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14110 uu____14112
                                  in
                               failwith uu____14108)))))

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
                      (fun uu____14148  ->
                         match uu____14148 with
                         | (x,i) ->
                             let uu____14167 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14167, i)) bs_lhs
                     in
                  let uu____14170 = lhs  in
                  match uu____14170 with
                  | (uu____14171,u_lhs,uu____14173) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14270 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14280 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14280, univ)
                             in
                          match uu____14270 with
                          | (k,univ) ->
                              let uu____14287 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14287 with
                               | (uu____14304,u,wl3) ->
                                   let uu____14307 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14307, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14333 =
                              let uu____14346 =
                                let uu____14357 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14357 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14408  ->
                                   fun uu____14409  ->
                                     match (uu____14408, uu____14409) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14510 =
                                           let uu____14517 =
                                             let uu____14520 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14520
                                              in
                                           copy_uvar u_lhs [] uu____14517 wl2
                                            in
                                         (match uu____14510 with
                                          | (uu____14549,t_a,wl3) ->
                                              let uu____14552 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14552 with
                                               | (uu____14571,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14346
                                ([], wl1)
                               in
                            (match uu____14333 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2124_14627 = ct  in
                                   let uu____14628 =
                                     let uu____14631 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14631
                                      in
                                   let uu____14646 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2124_14627.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2124_14627.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14628;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14646;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2124_14627.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2127_14664 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2127_14664.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2127_14664.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14667 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14667 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14705 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14705 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14716 =
                                          let uu____14721 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14721)  in
                                        TERM uu____14716  in
                                      let uu____14722 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14722 with
                                       | (sub_prob,wl3) ->
                                           let uu____14736 =
                                             let uu____14737 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14737
                                              in
                                           solve env uu____14736))
                             | (x,imp)::formals2 ->
                                 let uu____14759 =
                                   let uu____14766 =
                                     let uu____14769 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14769
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14766 wl1
                                    in
                                 (match uu____14759 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14790 =
                                          let uu____14793 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14793
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14790 u_x
                                         in
                                      let uu____14794 =
                                        let uu____14797 =
                                          let uu____14800 =
                                            let uu____14801 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14801, imp)  in
                                          [uu____14800]  in
                                        FStar_List.append bs_terms
                                          uu____14797
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14794 formals2 wl2)
                              in
                           let uu____14828 = occurs_check u_lhs arrow1  in
                           (match uu____14828 with
                            | (uu____14841,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14857 =
                                    FStar_Thunk.mk
                                      (fun uu____14861  ->
                                         let uu____14862 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14862)
                                     in
                                  giveup_or_defer env orig wl uu____14857
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
              (let uu____14895 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14895
               then
                 let uu____14900 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14903 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14900 (rel_to_string (p_rel orig)) uu____14903
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15034 = rhs wl1 scope env1 subst1  in
                     (match uu____15034 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15057 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15057
                            then
                              let uu____15062 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15062
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15140 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15140 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2197_15142 = hd1  in
                       let uu____15143 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2197_15142.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2197_15142.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15143
                       }  in
                     let hd21 =
                       let uu___2200_15147 = hd2  in
                       let uu____15148 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2200_15147.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2200_15147.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15148
                       }  in
                     let uu____15151 =
                       let uu____15156 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15156
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15151 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15179 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15179
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15186 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15186 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15258 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15258
                                  in
                               ((let uu____15276 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15276
                                 then
                                   let uu____15281 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15283 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15281
                                     uu____15283
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15318 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15354 = aux wl [] env [] bs1 bs2  in
               match uu____15354 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15413 = attempt sub_probs wl2  in
                   solve env1 uu____15413)

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
            let uu___2238_15433 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2238_15433.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2238_15433.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15445 = try_solve env wl'  in
          match uu____15445 with
          | Success (uu____15446,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2247_15450 = wl  in
                  {
                    attempting = (uu___2247_15450.attempting);
                    wl_deferred = (uu___2247_15450.wl_deferred);
                    ctr = (uu___2247_15450.ctr);
                    defer_ok = (uu___2247_15450.defer_ok);
                    smt_ok = (uu___2247_15450.smt_ok);
                    umax_heuristic_ok = (uu___2247_15450.umax_heuristic_ok);
                    tcenv = (uu___2247_15450.tcenv);
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
        (let uu____15459 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15459 wl)

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
              let uu____15473 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15473 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15507 = lhs1  in
              match uu____15507 with
              | (uu____15510,ctx_u,uu____15512) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15520 ->
                        let uu____15521 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15521 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15570 = quasi_pattern env1 lhs1  in
              match uu____15570 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15604) ->
                  let uu____15609 = lhs1  in
                  (match uu____15609 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15624 = occurs_check ctx_u rhs1  in
                       (match uu____15624 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15675 =
                                let uu____15683 =
                                  let uu____15685 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15685
                                   in
                                FStar_Util.Inl uu____15683  in
                              (uu____15675, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15713 =
                                 let uu____15715 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15715  in
                               if uu____15713
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15742 =
                                    let uu____15750 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15750  in
                                  let uu____15756 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15742, uu____15756)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15800 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15800 with
              | (rhs_hd,args) ->
                  let uu____15843 = FStar_Util.prefix args  in
                  (match uu____15843 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15915 = lhs1  in
                       (match uu____15915 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15919 =
                              let uu____15930 =
                                let uu____15937 =
                                  let uu____15940 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15940
                                   in
                                copy_uvar u_lhs [] uu____15937 wl1  in
                              match uu____15930 with
                              | (uu____15967,t_last_arg,wl2) ->
                                  let uu____15970 =
                                    let uu____15977 =
                                      let uu____15978 =
                                        let uu____15987 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____15987]  in
                                      FStar_List.append bs_lhs uu____15978
                                       in
                                    copy_uvar u_lhs uu____15977 t_res_lhs wl2
                                     in
                                  (match uu____15970 with
                                   | (uu____16022,lhs',wl3) ->
                                       let uu____16025 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16025 with
                                        | (uu____16042,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15919 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16063 =
                                     let uu____16064 =
                                       let uu____16069 =
                                         let uu____16070 =
                                           let uu____16073 =
                                             let uu____16078 =
                                               let uu____16079 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16079]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16078
                                              in
                                           uu____16073
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16070
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16069)  in
                                     TERM uu____16064  in
                                   [uu____16063]  in
                                 let uu____16104 =
                                   let uu____16111 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16111 with
                                   | (p1,wl3) ->
                                       let uu____16131 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16131 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16104 with
                                  | (sub_probs,wl3) ->
                                      let uu____16163 =
                                        let uu____16164 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16164  in
                                      solve env1 uu____16163))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16198 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16198 with
                | (uu____16216,args) ->
                    (match args with | [] -> false | uu____16252 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16271 =
                  let uu____16272 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16272.FStar_Syntax_Syntax.n  in
                match uu____16271 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16276 -> true
                | uu____16292 -> false  in
              let uu____16294 = quasi_pattern env1 lhs1  in
              match uu____16294 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    FStar_Thunk.mk
                      (fun uu____16312  ->
                         let uu____16313 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16313)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16322 = is_app rhs1  in
                  if uu____16322
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16327 = is_arrow rhs1  in
                     if uu____16327
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          FStar_Thunk.mk
                            (fun uu____16339  ->
                               let uu____16340 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16340)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16344 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16344
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16350 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16350
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16355 = lhs  in
                (match uu____16355 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16359 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16359 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16377 =
                              let uu____16381 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16381
                               in
                            FStar_All.pipe_right uu____16377
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16402 = occurs_check ctx_uv rhs1  in
                          (match uu____16402 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16431 =
                                   let uu____16432 =
                                     let uu____16434 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16434
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16432
                                    in
                                 giveup_or_defer env orig wl uu____16431
                               else
                                 (let uu____16442 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16442
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16449 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16449
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         FStar_Thunk.mk
                                           (fun uu____16462  ->
                                              let uu____16463 =
                                                names_to_string1 fvs2  in
                                              let uu____16465 =
                                                names_to_string1 fvs1  in
                                              let uu____16467 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16463 uu____16465
                                                uu____16467)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16479 ->
                          if wl.defer_ok
                          then
                            let uu____16483 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16483
                          else
                            (let uu____16488 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16488 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16514 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16514
                             | (FStar_Util.Inl msg,uu____16516) ->
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
                  let uu____16534 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16534
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16540 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16540
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16562 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16562
                else
                  (let uu____16567 =
                     let uu____16584 = quasi_pattern env lhs  in
                     let uu____16591 = quasi_pattern env rhs  in
                     (uu____16584, uu____16591)  in
                   match uu____16567 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16634 = lhs  in
                       (match uu____16634 with
                        | ({ FStar_Syntax_Syntax.n = uu____16635;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16637;_},u_lhs,uu____16639)
                            ->
                            let uu____16642 = rhs  in
                            (match uu____16642 with
                             | (uu____16643,u_rhs,uu____16645) ->
                                 let uu____16646 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16646
                                 then
                                   let uu____16653 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16653
                                 else
                                   (let uu____16656 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16656 with
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
                                        let uu____16688 =
                                          let uu____16695 =
                                            let uu____16698 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16698
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16695
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16688 with
                                         | (uu____16710,w,wl1) ->
                                             let w_app =
                                               let uu____16716 =
                                                 let uu____16721 =
                                                   FStar_List.map
                                                     (fun uu____16732  ->
                                                        match uu____16732
                                                        with
                                                        | (z,uu____16740) ->
                                                            let uu____16745 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16745) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16721
                                                  in
                                               uu____16716
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16747 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16747
                                               then
                                                 let uu____16752 =
                                                   let uu____16756 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16758 =
                                                     let uu____16762 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16764 =
                                                       let uu____16768 =
                                                         term_to_string w  in
                                                       let uu____16770 =
                                                         let uu____16774 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16783 =
                                                           let uu____16787 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16796 =
                                                             let uu____16800
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16800]
                                                              in
                                                           uu____16787 ::
                                                             uu____16796
                                                            in
                                                         uu____16774 ::
                                                           uu____16783
                                                          in
                                                       uu____16768 ::
                                                         uu____16770
                                                        in
                                                     uu____16762 ::
                                                       uu____16764
                                                      in
                                                   uu____16756 :: uu____16758
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16752
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16817 =
                                                     let uu____16822 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16822)  in
                                                   TERM uu____16817  in
                                                 let uu____16823 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16823
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16831 =
                                                        let uu____16836 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16836)
                                                         in
                                                      TERM uu____16831  in
                                                    [s1; s2])
                                                  in
                                               let uu____16837 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16837))))))
                   | uu____16838 ->
                       let uu____16855 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16855)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16909 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16909
            then
              let uu____16914 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16916 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16918 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16920 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16914 uu____16916 uu____16918 uu____16920
            else ());
           (let uu____16931 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16931 with
            | (head1,args1) ->
                let uu____16974 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____16974 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17044 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17044 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17049 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17049)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17070 =
                         FStar_Thunk.mk
                           (fun uu____17077  ->
                              let uu____17078 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17080 = args_to_string args1  in
                              let uu____17084 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17086 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17078 uu____17080 uu____17084
                                uu____17086)
                          in
                       giveup env1 uu____17070 orig
                     else
                       (let uu____17093 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17098 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17098 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17093
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2503_17102 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2503_17102.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2503_17102.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2503_17102.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2503_17102.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2503_17102.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2503_17102.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2503_17102.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2503_17102.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17112 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17112
                                    else solve env1 wl2))
                        else
                          (let uu____17117 = base_and_refinement env1 t1  in
                           match uu____17117 with
                           | (base1,refinement1) ->
                               let uu____17142 = base_and_refinement env1 t2
                                  in
                               (match uu____17142 with
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
                                           let uu____17307 =
                                             FStar_List.fold_right
                                               (fun uu____17347  ->
                                                  fun uu____17348  ->
                                                    match (uu____17347,
                                                            uu____17348)
                                                    with
                                                    | (((a1,uu____17400),
                                                        (a2,uu____17402)),
                                                       (probs,wl3)) ->
                                                        let uu____17451 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17451
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17307 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17494 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17494
                                                 then
                                                   let uu____17499 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17499
                                                 else ());
                                                (let uu____17505 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17505
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
                                                    (let uu____17532 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17532 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17548 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17548
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17556 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17556))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17581 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17581 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17597 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17597
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17605 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17605)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17633 =
                                           match uu____17633 with
                                           | (prob,reason) ->
                                               ((let uu____17650 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17650
                                                 then
                                                   let uu____17655 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17657 =
                                                     prob_to_string env2 prob
                                                      in
                                                   let uu____17659 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____17655 uu____17657
                                                     uu____17659
                                                 else ());
                                                (let uu____17665 =
                                                   let uu____17674 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17677 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17674, uu____17677)
                                                    in
                                                 match uu____17665 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17690 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17690 with
                                                      | (head1',uu____17708)
                                                          ->
                                                          let uu____17733 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17733
                                                           with
                                                           | (head2',uu____17751)
                                                               ->
                                                               let uu____17776
                                                                 =
                                                                 let uu____17781
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17782
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17781,
                                                                   uu____17782)
                                                                  in
                                                               (match uu____17776
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17784
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17784
                                                                    then
                                                                    let uu____17789
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17791
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17793
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17795
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17789
                                                                    uu____17791
                                                                    uu____17793
                                                                    uu____17795
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17800
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2591_17808
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2591_17808.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2591_17808.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2591_17808.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2591_17808.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2591_17808.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2591_17808.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2591_17808.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2591_17808.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17810
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17810
                                                                    then
                                                                    let uu____17815
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17815
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17820 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17832 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17832 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17840 =
                                             let uu____17841 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17841.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17840 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17846 -> false  in
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
                                          | uu____17849 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17852 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2611_17888 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2611_17888.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2611_17888.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2611_17888.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2611_17888.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2611_17888.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2611_17888.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2611_17888.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2611_17888.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17964 = destruct_flex_t scrutinee wl1  in
             match uu____17964 with
             | ((_t,uv,_args),wl2) ->
                 let uu____17975 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____17975 with
                  | (xs,pat_term,uu____17991,uu____17992) ->
                      let uu____17997 =
                        FStar_List.fold_left
                          (fun uu____18020  ->
                             fun x  ->
                               match uu____18020 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18041 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18041 with
                                    | (uu____18060,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____17997 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18081 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18081 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2651_18098 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2651_18098.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2651_18098.umax_heuristic_ok);
                                    tcenv = (uu___2651_18098.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18109 = solve env1 wl'  in
                                (match uu____18109 with
                                 | Success (uu____18112,imps) ->
                                     let wl'1 =
                                       let uu___2659_18115 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2659_18115.wl_deferred);
                                         ctr = (uu___2659_18115.ctr);
                                         defer_ok =
                                           (uu___2659_18115.defer_ok);
                                         smt_ok = (uu___2659_18115.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2659_18115.umax_heuristic_ok);
                                         tcenv = (uu___2659_18115.tcenv);
                                         wl_implicits =
                                           (uu___2659_18115.wl_implicits)
                                       }  in
                                     let uu____18116 = solve env1 wl'1  in
                                     (match uu____18116 with
                                      | Success (uu____18119,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2667_18123 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2667_18123.attempting);
                                                 wl_deferred =
                                                   (uu___2667_18123.wl_deferred);
                                                 ctr = (uu___2667_18123.ctr);
                                                 defer_ok =
                                                   (uu___2667_18123.defer_ok);
                                                 smt_ok =
                                                   (uu___2667_18123.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2667_18123.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2667_18123.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18124 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18130 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18153 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18153
                 then
                   let uu____18158 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18160 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18158 uu____18160
                 else ());
                (let uu____18165 =
                   let uu____18186 =
                     let uu____18195 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18195)  in
                   let uu____18202 =
                     let uu____18211 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18211)  in
                   (uu____18186, uu____18202)  in
                 match uu____18165 with
                 | ((uu____18241,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18244;
                                   FStar_Syntax_Syntax.vars = uu____18245;_}),
                    (s,t)) ->
                     let uu____18316 =
                       let uu____18318 = is_flex scrutinee  in
                       Prims.op_Negation uu____18318  in
                     if uu____18316
                     then
                       ((let uu____18329 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18329
                         then
                           let uu____18334 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18334
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18353 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18353
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18368 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18368
                           then
                             let uu____18373 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18375 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18373 uu____18375
                           else ());
                          (let pat_discriminates uu___28_18400 =
                             match uu___28_18400 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18416;
                                  FStar_Syntax_Syntax.p = uu____18417;_},FStar_Pervasives_Native.None
                                ,uu____18418) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18432;
                                  FStar_Syntax_Syntax.p = uu____18433;_},FStar_Pervasives_Native.None
                                ,uu____18434) -> true
                             | uu____18461 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18564 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18564 with
                                       | (uu____18566,uu____18567,t') ->
                                           let uu____18585 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18585 with
                                            | (FullMatch ,uu____18597) ->
                                                true
                                            | (HeadMatch
                                               uu____18611,uu____18612) ->
                                                true
                                            | uu____18627 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18664 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18664
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18675 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18675 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18763,uu____18764) ->
                                       branches1
                                   | uu____18909 -> branches  in
                                 let uu____18964 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____18973 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____18973 with
                                        | (p,uu____18977,uu____18978) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19007  -> FStar_Util.Inr _19007)
                                   uu____18964))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19037 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19037 with
                                | (p,uu____19046,e) ->
                                    ((let uu____19065 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19065
                                      then
                                        let uu____19070 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19072 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19070 uu____19072
                                      else ());
                                     (let uu____19077 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19092  -> FStar_Util.Inr _19092)
                                        uu____19077)))))
                 | ((s,t),(uu____19095,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19098;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19099;_}))
                     ->
                     let uu____19168 =
                       let uu____19170 = is_flex scrutinee  in
                       Prims.op_Negation uu____19170  in
                     if uu____19168
                     then
                       ((let uu____19181 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19181
                         then
                           let uu____19186 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19186
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19205 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19205
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19220 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19220
                           then
                             let uu____19225 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19227 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19225 uu____19227
                           else ());
                          (let pat_discriminates uu___28_19252 =
                             match uu___28_19252 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19268;
                                  FStar_Syntax_Syntax.p = uu____19269;_},FStar_Pervasives_Native.None
                                ,uu____19270) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19284;
                                  FStar_Syntax_Syntax.p = uu____19285;_},FStar_Pervasives_Native.None
                                ,uu____19286) -> true
                             | uu____19313 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19416 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19416 with
                                       | (uu____19418,uu____19419,t') ->
                                           let uu____19437 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19437 with
                                            | (FullMatch ,uu____19449) ->
                                                true
                                            | (HeadMatch
                                               uu____19463,uu____19464) ->
                                                true
                                            | uu____19479 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19516 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19516
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19527 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19527 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19615,uu____19616) ->
                                       branches1
                                   | uu____19761 -> branches  in
                                 let uu____19816 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19825 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19825 with
                                        | (p,uu____19829,uu____19830) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19859  -> FStar_Util.Inr _19859)
                                   uu____19816))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19889 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19889 with
                                | (p,uu____19898,e) ->
                                    ((let uu____19917 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19917
                                      then
                                        let uu____19922 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19924 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19922 uu____19924
                                      else ());
                                     (let uu____19929 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19944  -> FStar_Util.Inr _19944)
                                        uu____19929)))))
                 | uu____19945 ->
                     ((let uu____19967 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19967
                       then
                         let uu____19972 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____19974 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____19972 uu____19974
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20020 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20020
            then
              let uu____20025 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20027 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20029 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20031 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20025 uu____20027 uu____20029 uu____20031
            else ());
           (let uu____20036 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20036 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20067,uu____20068) ->
                     let rec may_relate head3 =
                       let uu____20096 =
                         let uu____20097 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20097.FStar_Syntax_Syntax.n  in
                       match uu____20096 with
                       | FStar_Syntax_Syntax.Tm_name uu____20101 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20103 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20128 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20128 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20130 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20133
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20134 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20137,uu____20138) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20180) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20186) ->
                           may_relate t
                       | uu____20191 -> false  in
                     let uu____20193 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20193 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20206 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20206
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20216 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20216
                          then
                            let uu____20219 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20219 with
                             | (guard,wl2) ->
                                 let uu____20226 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20226)
                          else
                            (let uu____20229 =
                               FStar_Thunk.mk
                                 (fun uu____20236  ->
                                    let uu____20237 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20239 =
                                      let uu____20241 =
                                        let uu____20245 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20245
                                          (fun x  ->
                                             let uu____20252 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20252)
                                         in
                                      FStar_Util.dflt "" uu____20241  in
                                    let uu____20257 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20259 =
                                      let uu____20261 =
                                        let uu____20265 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20265
                                          (fun x  ->
                                             let uu____20272 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20272)
                                         in
                                      FStar_Util.dflt "" uu____20261  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20237 uu____20239 uu____20257
                                      uu____20259)
                                in
                             giveup env1 uu____20229 orig))
                 | (HeadMatch (true ),uu____20278) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20293 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20293 with
                        | (guard,wl2) ->
                            let uu____20300 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20300)
                     else
                       (let uu____20303 =
                          FStar_Thunk.mk
                            (fun uu____20308  ->
                               let uu____20309 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20311 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20309 uu____20311)
                           in
                        giveup env1 uu____20303 orig)
                 | (uu____20314,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2842_20328 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2842_20328.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2842_20328.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2842_20328.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2842_20328.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2842_20328.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2842_20328.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2842_20328.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2842_20328.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20355 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20355
          then
            let uu____20358 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20358
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20364 =
                let uu____20367 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20367  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20364 t1);
             (let uu____20386 =
                let uu____20389 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20389  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20386 t2);
             (let uu____20408 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20408
              then
                let uu____20412 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20414 =
                  let uu____20416 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20418 =
                    let uu____20420 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20420  in
                  Prims.op_Hat uu____20416 uu____20418  in
                let uu____20423 =
                  let uu____20425 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20427 =
                    let uu____20429 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20429  in
                  Prims.op_Hat uu____20425 uu____20427  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20412 uu____20414 uu____20423
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20436,uu____20437) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20453,FStar_Syntax_Syntax.Tm_delayed uu____20454) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20470,uu____20471) ->
                  let uu____20498 =
                    let uu___2873_20499 = problem  in
                    let uu____20500 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2873_20499.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20500;
                      FStar_TypeChecker_Common.relation =
                        (uu___2873_20499.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2873_20499.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2873_20499.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2873_20499.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2873_20499.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2873_20499.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2873_20499.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2873_20499.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20498 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20501,uu____20502) ->
                  let uu____20509 =
                    let uu___2879_20510 = problem  in
                    let uu____20511 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2879_20510.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20511;
                      FStar_TypeChecker_Common.relation =
                        (uu___2879_20510.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2879_20510.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2879_20510.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2879_20510.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2879_20510.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2879_20510.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2879_20510.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2879_20510.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20509 wl
              | (uu____20512,FStar_Syntax_Syntax.Tm_ascribed uu____20513) ->
                  let uu____20540 =
                    let uu___2885_20541 = problem  in
                    let uu____20542 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2885_20541.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2885_20541.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2885_20541.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20542;
                      FStar_TypeChecker_Common.element =
                        (uu___2885_20541.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2885_20541.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2885_20541.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2885_20541.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2885_20541.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2885_20541.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20540 wl
              | (uu____20543,FStar_Syntax_Syntax.Tm_meta uu____20544) ->
                  let uu____20551 =
                    let uu___2891_20552 = problem  in
                    let uu____20553 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2891_20552.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2891_20552.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2891_20552.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20553;
                      FStar_TypeChecker_Common.element =
                        (uu___2891_20552.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2891_20552.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2891_20552.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2891_20552.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2891_20552.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2891_20552.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20551 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20555),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20557)) ->
                  let uu____20566 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20566
              | (FStar_Syntax_Syntax.Tm_bvar uu____20567,uu____20568) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20570,FStar_Syntax_Syntax.Tm_bvar uu____20571) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20641 =
                    match uu___29_20641 with
                    | [] -> c
                    | bs ->
                        let uu____20669 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20669
                     in
                  let uu____20680 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20680 with
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
                                    let uu____20829 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20829
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
                  let mk_t t l uu___30_20918 =
                    match uu___30_20918 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____20960 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____20960 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21105 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21106 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21105
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21106 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21108,uu____21109) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21140 -> true
                    | uu____21160 -> false  in
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
                      (let uu____21220 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2993_21228 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2993_21228.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2993_21228.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2993_21228.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2993_21228.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2993_21228.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2993_21228.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2993_21228.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2993_21228.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2993_21228.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2993_21228.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2993_21228.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2993_21228.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2993_21228.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2993_21228.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2993_21228.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2993_21228.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___2993_21228.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2993_21228.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2993_21228.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2993_21228.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2993_21228.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2993_21228.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2993_21228.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2993_21228.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2993_21228.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2993_21228.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2993_21228.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2993_21228.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2993_21228.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2993_21228.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2993_21228.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2993_21228.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2993_21228.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2993_21228.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2993_21228.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___2993_21228.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2993_21228.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2993_21228.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2993_21228.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2993_21228.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2993_21228.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2993_21228.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2993_21228.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2993_21228.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21220 with
                       | (uu____21233,ty,uu____21235) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21244 =
                                 let uu____21245 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21245.FStar_Syntax_Syntax.n  in
                               match uu____21244 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21248 ->
                                   let uu____21255 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21255
                               | uu____21256 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21259 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21259
                             then
                               let uu____21264 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21266 =
                                 let uu____21268 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21268
                                  in
                               let uu____21269 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21264 uu____21266 uu____21269
                             else ());
                            r1))
                     in
                  let uu____21274 =
                    let uu____21291 = maybe_eta t1  in
                    let uu____21298 = maybe_eta t2  in
                    (uu____21291, uu____21298)  in
                  (match uu____21274 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3014_21340 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3014_21340.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3014_21340.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3014_21340.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3014_21340.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3014_21340.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3014_21340.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3014_21340.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3014_21340.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21361 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21361
                       then
                         let uu____21364 = destruct_flex_t not_abs wl  in
                         (match uu____21364 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21381 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21381.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21381.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21381.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21381.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21381.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21381.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21381.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21381.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21384 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21384 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21407 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21407
                       then
                         let uu____21410 = destruct_flex_t not_abs wl  in
                         (match uu____21410 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21427 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21427.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21427.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21427.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21427.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21427.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21427.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21427.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21427.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21430 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21430 orig))
                   | uu____21433 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21451,FStar_Syntax_Syntax.Tm_abs uu____21452) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21483 -> true
                    | uu____21503 -> false  in
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
                      (let uu____21563 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2993_21571 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2993_21571.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2993_21571.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2993_21571.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2993_21571.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2993_21571.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2993_21571.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2993_21571.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2993_21571.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2993_21571.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2993_21571.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2993_21571.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2993_21571.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2993_21571.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2993_21571.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2993_21571.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2993_21571.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___2993_21571.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2993_21571.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2993_21571.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2993_21571.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2993_21571.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2993_21571.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2993_21571.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2993_21571.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2993_21571.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2993_21571.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2993_21571.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2993_21571.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2993_21571.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2993_21571.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2993_21571.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2993_21571.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2993_21571.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2993_21571.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2993_21571.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___2993_21571.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2993_21571.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2993_21571.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2993_21571.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2993_21571.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2993_21571.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2993_21571.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2993_21571.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2993_21571.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21563 with
                       | (uu____21576,ty,uu____21578) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21587 =
                                 let uu____21588 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21588.FStar_Syntax_Syntax.n  in
                               match uu____21587 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21591 ->
                                   let uu____21598 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21598
                               | uu____21599 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21602 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21602
                             then
                               let uu____21607 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21609 =
                                 let uu____21611 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21611
                                  in
                               let uu____21612 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21607 uu____21609 uu____21612
                             else ());
                            r1))
                     in
                  let uu____21617 =
                    let uu____21634 = maybe_eta t1  in
                    let uu____21641 = maybe_eta t2  in
                    (uu____21634, uu____21641)  in
                  (match uu____21617 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3014_21683 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3014_21683.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3014_21683.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3014_21683.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3014_21683.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3014_21683.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3014_21683.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3014_21683.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3014_21683.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21704 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21704
                       then
                         let uu____21707 = destruct_flex_t not_abs wl  in
                         (match uu____21707 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21724 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21724.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21724.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21724.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21724.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21724.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21724.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21724.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21724.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21727 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21727 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21750 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21750
                       then
                         let uu____21753 = destruct_flex_t not_abs wl  in
                         (match uu____21753 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21770 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21770.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21770.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21770.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21770.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21770.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21770.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21770.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21770.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21773 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21773 orig))
                   | uu____21776 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21806 =
                    let uu____21811 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21811 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3054_21839 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3054_21839.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3054_21839.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3056_21841 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3056_21841.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3056_21841.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21842,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3054_21857 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3054_21857.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3054_21857.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3056_21859 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3056_21859.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3056_21859.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21860 -> (x1, x2)  in
                  (match uu____21806 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21879 = as_refinement false env t11  in
                       (match uu____21879 with
                        | (x12,phi11) ->
                            let uu____21887 = as_refinement false env t21  in
                            (match uu____21887 with
                             | (x22,phi21) ->
                                 ((let uu____21896 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21896
                                   then
                                     ((let uu____21901 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21903 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21905 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21901
                                         uu____21903 uu____21905);
                                      (let uu____21908 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21910 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21912 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21908
                                         uu____21910 uu____21912))
                                   else ());
                                  (let uu____21917 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21917 with
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
                                         let uu____21988 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____21988
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22000 =
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
                                         (let uu____22013 =
                                            let uu____22016 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22016
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22013
                                            (p_guard base_prob));
                                         (let uu____22035 =
                                            let uu____22038 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22038
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22035
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22057 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22057)
                                          in
                                       let has_uvars =
                                         (let uu____22062 =
                                            let uu____22064 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22064
                                             in
                                          Prims.op_Negation uu____22062) ||
                                           (let uu____22068 =
                                              let uu____22070 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22070
                                               in
                                            Prims.op_Negation uu____22068)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22074 =
                                           let uu____22079 =
                                             let uu____22088 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22088]  in
                                           mk_t_problem wl1 uu____22079 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22074 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22111 =
                                                solve env1
                                                  (let uu___3099_22113 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3099_22113.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3099_22113.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3099_22113.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3099_22113.tcenv);
                                                     wl_implicits =
                                                       (uu___3099_22113.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22111 with
                                               | Failed (prob,msg) ->
                                                   (FStar_Syntax_Unionfind.rollback
                                                      tx;
                                                    if
                                                      ((Prims.op_Negation
                                                          env1.FStar_TypeChecker_Env.uvar_subtyping)
                                                         && has_uvars)
                                                        ||
                                                        (Prims.op_Negation
                                                           wl2.smt_ok)
                                                    then giveup env1 msg prob
                                                    else fallback ())
                                               | Success uu____22128 ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22137 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22137
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3112_22146 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3112_22146.attempting);
                                                         wl_deferred =
                                                           (uu___3112_22146.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3112_22146.defer_ok);
                                                         smt_ok =
                                                           (uu___3112_22146.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3112_22146.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3112_22146.tcenv);
                                                         wl_implicits =
                                                           (uu___3112_22146.wl_implicits)
                                                       }  in
                                                     let uu____22148 =
                                                       attempt [base_prob]
                                                         wl4
                                                        in
                                                     solve env1 uu____22148))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22151,FStar_Syntax_Syntax.Tm_uvar uu____22152) ->
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
                    FStar_Syntax_Syntax.vars = uu____22193;_},uu____22194),FStar_Syntax_Syntax.Tm_uvar
                 uu____22195) ->
                  let uu____22244 = destruct_flex_t t1 wl  in
                  (match uu____22244 with
                   | (f1,wl1) ->
                       let uu____22251 = destruct_flex_t t2 wl1  in
                       (match uu____22251 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22258,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22259;
                    FStar_Syntax_Syntax.pos = uu____22260;
                    FStar_Syntax_Syntax.vars = uu____22261;_},uu____22262))
                  ->
                  let uu____22311 = destruct_flex_t t1 wl  in
                  (match uu____22311 with
                   | (f1,wl1) ->
                       let uu____22318 = destruct_flex_t t2 wl1  in
                       (match uu____22318 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22325;
                    FStar_Syntax_Syntax.pos = uu____22326;
                    FStar_Syntax_Syntax.vars = uu____22327;_},uu____22328),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22329;
                    FStar_Syntax_Syntax.pos = uu____22330;
                    FStar_Syntax_Syntax.vars = uu____22331;_},uu____22332))
                  ->
                  let uu____22405 = destruct_flex_t t1 wl  in
                  (match uu____22405 with
                   | (f1,wl1) ->
                       let uu____22412 = destruct_flex_t t2 wl1  in
                       (match uu____22412 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22419,uu____22420) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22433 = destruct_flex_t t1 wl  in
                  (match uu____22433 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22440;
                    FStar_Syntax_Syntax.pos = uu____22441;
                    FStar_Syntax_Syntax.vars = uu____22442;_},uu____22443),uu____22444)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22481 = destruct_flex_t t1 wl  in
                  (match uu____22481 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22488,FStar_Syntax_Syntax.Tm_uvar uu____22489) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22502,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22503;
                    FStar_Syntax_Syntax.pos = uu____22504;
                    FStar_Syntax_Syntax.vars = uu____22505;_},uu____22506))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22543,FStar_Syntax_Syntax.Tm_arrow uu____22544) ->
                  solve_t' env
                    (let uu___3212_22572 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3212_22572.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3212_22572.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3212_22572.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3212_22572.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3212_22572.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3212_22572.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3212_22572.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3212_22572.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3212_22572.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22573;
                    FStar_Syntax_Syntax.pos = uu____22574;
                    FStar_Syntax_Syntax.vars = uu____22575;_},uu____22576),FStar_Syntax_Syntax.Tm_arrow
                 uu____22577) ->
                  solve_t' env
                    (let uu___3212_22629 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3212_22629.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3212_22629.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3212_22629.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3212_22629.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3212_22629.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3212_22629.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3212_22629.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3212_22629.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3212_22629.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22630,FStar_Syntax_Syntax.Tm_uvar uu____22631) ->
                  let uu____22644 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22644
              | (uu____22645,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22646;
                    FStar_Syntax_Syntax.pos = uu____22647;
                    FStar_Syntax_Syntax.vars = uu____22648;_},uu____22649))
                  ->
                  let uu____22686 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22686
              | (FStar_Syntax_Syntax.Tm_uvar uu____22687,uu____22688) ->
                  let uu____22701 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22701
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22702;
                    FStar_Syntax_Syntax.pos = uu____22703;
                    FStar_Syntax_Syntax.vars = uu____22704;_},uu____22705),uu____22706)
                  ->
                  let uu____22743 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22743
              | (FStar_Syntax_Syntax.Tm_refine uu____22744,uu____22745) ->
                  let t21 =
                    let uu____22753 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22753  in
                  solve_t env
                    (let uu___3247_22779 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3247_22779.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3247_22779.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3247_22779.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3247_22779.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3247_22779.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3247_22779.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3247_22779.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3247_22779.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3247_22779.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22780,FStar_Syntax_Syntax.Tm_refine uu____22781) ->
                  let t11 =
                    let uu____22789 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22789  in
                  solve_t env
                    (let uu___3254_22815 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3254_22815.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3254_22815.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3254_22815.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3254_22815.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3254_22815.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3254_22815.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3254_22815.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3254_22815.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3254_22815.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22897 =
                    let uu____22898 = guard_of_prob env wl problem t1 t2  in
                    match uu____22898 with
                    | (guard,wl1) ->
                        let uu____22905 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22905
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23124 = br1  in
                        (match uu____23124 with
                         | (p1,w1,uu____23153) ->
                             let uu____23170 = br2  in
                             (match uu____23170 with
                              | (p2,w2,uu____23193) ->
                                  let uu____23198 =
                                    let uu____23200 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23200  in
                                  if uu____23198
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23227 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23227 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23264 = br2  in
                                         (match uu____23264 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23297 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23297
                                                 in
                                              let uu____23302 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23333,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23354) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23413 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23413 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23302
                                                (fun uu____23485  ->
                                                   match uu____23485 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23522 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23522
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23543
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23543
                                                              then
                                                                let uu____23548
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23550
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23548
                                                                  uu____23550
                                                              else ());
                                                             (let uu____23556
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23556
                                                                (fun
                                                                   uu____23592
                                                                    ->
                                                                   match uu____23592
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
                    | uu____23721 -> FStar_Pervasives_Native.None  in
                  let uu____23762 = solve_branches wl brs1 brs2  in
                  (match uu____23762 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23788 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23788 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23815 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23815 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23849 =
                                FStar_List.map
                                  (fun uu____23861  ->
                                     match uu____23861 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23849  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23870 =
                              let uu____23871 =
                                let uu____23872 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23872
                                  (let uu___3353_23880 = wl3  in
                                   {
                                     attempting =
                                       (uu___3353_23880.attempting);
                                     wl_deferred =
                                       (uu___3353_23880.wl_deferred);
                                     ctr = (uu___3353_23880.ctr);
                                     defer_ok = (uu___3353_23880.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3353_23880.umax_heuristic_ok);
                                     tcenv = (uu___3353_23880.tcenv);
                                     wl_implicits =
                                       (uu___3353_23880.wl_implicits)
                                   })
                                 in
                              solve env uu____23871  in
                            (match uu____23870 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23885 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____23894 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____23894 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____23897,uu____23898) ->
                  let head1 =
                    let uu____23922 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23922
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23968 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23968
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24014 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24014
                    then
                      let uu____24018 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24020 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24022 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24018 uu____24020 uu____24022
                    else ());
                   (let no_free_uvars t =
                      (let uu____24036 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24036) &&
                        (let uu____24040 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24040)
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
                      let uu____24059 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24059 = FStar_Syntax_Util.Equal  in
                    let uu____24060 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24060
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24064 = equal t1 t2  in
                         (if uu____24064
                          then
                            let uu____24067 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24067
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24072 =
                            let uu____24079 = equal t1 t2  in
                            if uu____24079
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24092 = mk_eq2 wl env orig t1 t2  in
                               match uu____24092 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24072 with
                          | (guard,wl1) ->
                              let uu____24113 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24113))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24116,uu____24117) ->
                  let head1 =
                    let uu____24125 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24125
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24171 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24171
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24217 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24217
                    then
                      let uu____24221 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24223 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24225 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24221 uu____24223 uu____24225
                    else ());
                   (let no_free_uvars t =
                      (let uu____24239 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24239) &&
                        (let uu____24243 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24243)
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
                      let uu____24262 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24262 = FStar_Syntax_Util.Equal  in
                    let uu____24263 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24263
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24267 = equal t1 t2  in
                         (if uu____24267
                          then
                            let uu____24270 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24270
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24275 =
                            let uu____24282 = equal t1 t2  in
                            if uu____24282
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24295 = mk_eq2 wl env orig t1 t2  in
                               match uu____24295 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24275 with
                          | (guard,wl1) ->
                              let uu____24316 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24316))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24319,uu____24320) ->
                  let head1 =
                    let uu____24322 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24322
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24368 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24368
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24414 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24414
                    then
                      let uu____24418 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24420 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24422 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24418 uu____24420 uu____24422
                    else ());
                   (let no_free_uvars t =
                      (let uu____24436 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24436) &&
                        (let uu____24440 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24440)
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
                      let uu____24459 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24459 = FStar_Syntax_Util.Equal  in
                    let uu____24460 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24460
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24464 = equal t1 t2  in
                         (if uu____24464
                          then
                            let uu____24467 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24467
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24472 =
                            let uu____24479 = equal t1 t2  in
                            if uu____24479
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24492 = mk_eq2 wl env orig t1 t2  in
                               match uu____24492 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24472 with
                          | (guard,wl1) ->
                              let uu____24513 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24513))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24516,uu____24517) ->
                  let head1 =
                    let uu____24519 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24519
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24565 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24565
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24611 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24611
                    then
                      let uu____24615 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24617 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24619 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24615 uu____24617 uu____24619
                    else ());
                   (let no_free_uvars t =
                      (let uu____24633 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24633) &&
                        (let uu____24637 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24637)
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
                      let uu____24656 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24656 = FStar_Syntax_Util.Equal  in
                    let uu____24657 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24657
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24661 = equal t1 t2  in
                         (if uu____24661
                          then
                            let uu____24664 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24664
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24669 =
                            let uu____24676 = equal t1 t2  in
                            if uu____24676
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24689 = mk_eq2 wl env orig t1 t2  in
                               match uu____24689 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24669 with
                          | (guard,wl1) ->
                              let uu____24710 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24710))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24713,uu____24714) ->
                  let head1 =
                    let uu____24716 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24716
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24762 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24762
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24808 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24808
                    then
                      let uu____24812 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24814 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24816 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24812 uu____24814 uu____24816
                    else ());
                   (let no_free_uvars t =
                      (let uu____24830 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24830) &&
                        (let uu____24834 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24834)
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
                      let uu____24853 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24853 = FStar_Syntax_Util.Equal  in
                    let uu____24854 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24854
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24858 = equal t1 t2  in
                         (if uu____24858
                          then
                            let uu____24861 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24861
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24866 =
                            let uu____24873 = equal t1 t2  in
                            if uu____24873
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24886 = mk_eq2 wl env orig t1 t2  in
                               match uu____24886 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24866 with
                          | (guard,wl1) ->
                              let uu____24907 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24907))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24910,uu____24911) ->
                  let head1 =
                    let uu____24929 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24929
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24975 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24975
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25021 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25021
                    then
                      let uu____25025 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25027 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25029 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25025 uu____25027 uu____25029
                    else ());
                   (let no_free_uvars t =
                      (let uu____25043 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25043) &&
                        (let uu____25047 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25047)
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
                      let uu____25066 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25066 = FStar_Syntax_Util.Equal  in
                    let uu____25067 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25067
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25071 = equal t1 t2  in
                         (if uu____25071
                          then
                            let uu____25074 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25074
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25079 =
                            let uu____25086 = equal t1 t2  in
                            if uu____25086
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25099 = mk_eq2 wl env orig t1 t2  in
                               match uu____25099 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25079 with
                          | (guard,wl1) ->
                              let uu____25120 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25120))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25123,FStar_Syntax_Syntax.Tm_match uu____25124) ->
                  let head1 =
                    let uu____25148 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25148
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25194 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25194
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25240 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25240
                    then
                      let uu____25244 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25246 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25248 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25244 uu____25246 uu____25248
                    else ());
                   (let no_free_uvars t =
                      (let uu____25262 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25262) &&
                        (let uu____25266 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25266)
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
                      let uu____25285 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25285 = FStar_Syntax_Util.Equal  in
                    let uu____25286 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25286
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25290 = equal t1 t2  in
                         (if uu____25290
                          then
                            let uu____25293 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25293
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25298 =
                            let uu____25305 = equal t1 t2  in
                            if uu____25305
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25318 = mk_eq2 wl env orig t1 t2  in
                               match uu____25318 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25298 with
                          | (guard,wl1) ->
                              let uu____25339 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25339))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25342,FStar_Syntax_Syntax.Tm_uinst uu____25343) ->
                  let head1 =
                    let uu____25351 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25351
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25397 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25397
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25443 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25443
                    then
                      let uu____25447 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25449 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25451 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25447 uu____25449 uu____25451
                    else ());
                   (let no_free_uvars t =
                      (let uu____25465 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25465) &&
                        (let uu____25469 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25469)
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
                      let uu____25488 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25488 = FStar_Syntax_Util.Equal  in
                    let uu____25489 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25489
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25493 = equal t1 t2  in
                         (if uu____25493
                          then
                            let uu____25496 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25496
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25501 =
                            let uu____25508 = equal t1 t2  in
                            if uu____25508
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25521 = mk_eq2 wl env orig t1 t2  in
                               match uu____25521 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25501 with
                          | (guard,wl1) ->
                              let uu____25542 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25542))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25545,FStar_Syntax_Syntax.Tm_name uu____25546) ->
                  let head1 =
                    let uu____25548 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25548
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25594 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25594
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25634 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25634
                    then
                      let uu____25638 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25640 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25642 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25638 uu____25640 uu____25642
                    else ());
                   (let no_free_uvars t =
                      (let uu____25656 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25656) &&
                        (let uu____25660 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25660)
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
                      let uu____25679 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25679 = FStar_Syntax_Util.Equal  in
                    let uu____25680 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25680
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25684 = equal t1 t2  in
                         (if uu____25684
                          then
                            let uu____25687 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25687
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25692 =
                            let uu____25699 = equal t1 t2  in
                            if uu____25699
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25712 = mk_eq2 wl env orig t1 t2  in
                               match uu____25712 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25692 with
                          | (guard,wl1) ->
                              let uu____25733 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25733))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25736,FStar_Syntax_Syntax.Tm_constant uu____25737) ->
                  let head1 =
                    let uu____25739 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25739
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25779 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25779
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25819 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25819
                    then
                      let uu____25823 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25825 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25827 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25823 uu____25825 uu____25827
                    else ());
                   (let no_free_uvars t =
                      (let uu____25841 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25841) &&
                        (let uu____25845 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25845)
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
                      let uu____25864 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25864 = FStar_Syntax_Util.Equal  in
                    let uu____25865 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25865
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25869 = equal t1 t2  in
                         (if uu____25869
                          then
                            let uu____25872 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25872
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25877 =
                            let uu____25884 = equal t1 t2  in
                            if uu____25884
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25897 = mk_eq2 wl env orig t1 t2  in
                               match uu____25897 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25877 with
                          | (guard,wl1) ->
                              let uu____25918 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25918))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25921,FStar_Syntax_Syntax.Tm_fvar uu____25922) ->
                  let head1 =
                    let uu____25924 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25924
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25970 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25970
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26016 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26016
                    then
                      let uu____26020 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26022 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26024 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26020 uu____26022 uu____26024
                    else ());
                   (let no_free_uvars t =
                      (let uu____26038 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26038) &&
                        (let uu____26042 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26042)
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
                      let uu____26061 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26061 = FStar_Syntax_Util.Equal  in
                    let uu____26062 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26062
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26066 = equal t1 t2  in
                         (if uu____26066
                          then
                            let uu____26069 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26069
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26074 =
                            let uu____26081 = equal t1 t2  in
                            if uu____26081
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26094 = mk_eq2 wl env orig t1 t2  in
                               match uu____26094 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26074 with
                          | (guard,wl1) ->
                              let uu____26115 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26115))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26118,FStar_Syntax_Syntax.Tm_app uu____26119) ->
                  let head1 =
                    let uu____26137 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26137
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26177 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26177
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26217 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26217
                    then
                      let uu____26221 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26223 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26225 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26221 uu____26223 uu____26225
                    else ());
                   (let no_free_uvars t =
                      (let uu____26239 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26239) &&
                        (let uu____26243 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26243)
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
                      let uu____26262 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26262 = FStar_Syntax_Util.Equal  in
                    let uu____26263 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26263
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26267 = equal t1 t2  in
                         (if uu____26267
                          then
                            let uu____26270 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26270
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26275 =
                            let uu____26282 = equal t1 t2  in
                            if uu____26282
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26295 = mk_eq2 wl env orig t1 t2  in
                               match uu____26295 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26275 with
                          | (guard,wl1) ->
                              let uu____26316 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26316))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26319,FStar_Syntax_Syntax.Tm_let uu____26320) ->
                  let uu____26347 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26347
                  then
                    let uu____26350 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26350
                  else
                    (let uu____26353 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26353 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26356,uu____26357) ->
                  let uu____26371 =
                    let uu____26377 =
                      let uu____26379 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26381 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26383 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26385 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26379 uu____26381 uu____26383 uu____26385
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26377)
                     in
                  FStar_Errors.raise_error uu____26371
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26389,FStar_Syntax_Syntax.Tm_let uu____26390) ->
                  let uu____26404 =
                    let uu____26410 =
                      let uu____26412 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26414 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26416 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26418 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26412 uu____26414 uu____26416 uu____26418
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26410)
                     in
                  FStar_Errors.raise_error uu____26404
                    t1.FStar_Syntax_Syntax.pos
              | uu____26422 ->
                  let uu____26427 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26427 orig))))

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
          (let uu____26493 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26493
           then
             let uu____26498 =
               let uu____26500 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26500  in
             let uu____26501 =
               let uu____26503 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26503  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26498 uu____26501
           else ());
          (let uu____26507 =
             let uu____26509 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26509  in
           if uu____26507
           then
             let uu____26512 =
               FStar_Thunk.mk
                 (fun uu____26517  ->
                    let uu____26518 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26520 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26518 uu____26520)
                in
             giveup env uu____26512 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26542 =
                  FStar_Thunk.mk
                    (fun uu____26547  ->
                       let uu____26548 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26550 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26548 uu____26550)
                   in
                giveup env uu____26542 orig)
             else
               (let uu____26555 =
                  FStar_List.fold_left2
                    (fun uu____26576  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26576 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26597 =
                                 let uu____26602 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26603 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26602
                                   FStar_TypeChecker_Common.EQ uu____26603
                                   "effect universes"
                                  in
                               (match uu____26597 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26555 with
                | (univ_sub_probs,wl1) ->
                    let uu____26623 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26623 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26631 =
                           FStar_List.fold_right2
                             (fun uu____26668  ->
                                fun uu____26669  ->
                                  fun uu____26670  ->
                                    match (uu____26668, uu____26669,
                                            uu____26670)
                                    with
                                    | ((a1,uu____26714),(a2,uu____26716),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26749 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26749 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26631 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26776 =
                                  let uu____26779 =
                                    let uu____26782 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26782
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26779
                                   in
                                FStar_List.append univ_sub_probs uu____26776
                                 in
                              let guard =
                                let guard =
                                  let uu____26804 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26804  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3505_26813 = wl3  in
                                {
                                  attempting = (uu___3505_26813.attempting);
                                  wl_deferred = (uu___3505_26813.wl_deferred);
                                  ctr = (uu___3505_26813.ctr);
                                  defer_ok = (uu___3505_26813.defer_ok);
                                  smt_ok = (uu___3505_26813.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3505_26813.umax_heuristic_ok);
                                  tcenv = (uu___3505_26813.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26815 = attempt sub_probs wl5  in
                              solve env uu____26815))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26833 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26833
           then
             let uu____26838 =
               let uu____26840 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26840
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26842 =
               let uu____26844 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26844
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26838 uu____26842
           else ());
          (let uu____26849 =
             let uu____26854 =
               let uu____26859 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26859
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26854
               (fun uu____26876  ->
                  match uu____26876 with
                  | (c,g) ->
                      let uu____26887 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26887, g))
              in
           match uu____26849 with
           | (c12,g_lift) ->
               ((let uu____26891 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26891
                 then
                   let uu____26896 =
                     let uu____26898 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26898
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26900 =
                     let uu____26902 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26902
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26896 uu____26900
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3525_26912 = wl  in
                     {
                       attempting = (uu___3525_26912.attempting);
                       wl_deferred = (uu___3525_26912.wl_deferred);
                       ctr = (uu___3525_26912.ctr);
                       defer_ok = (uu___3525_26912.defer_ok);
                       smt_ok = (uu___3525_26912.smt_ok);
                       umax_heuristic_ok =
                         (uu___3525_26912.umax_heuristic_ok);
                       tcenv = (uu___3525_26912.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26913 =
                     let rec is_uvar1 t =
                       let uu____26927 =
                         let uu____26928 = FStar_Syntax_Subst.compress t  in
                         uu____26928.FStar_Syntax_Syntax.n  in
                       match uu____26927 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26932 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____26947) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____26953) ->
                           is_uvar1 t1
                       | uu____26978 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27012  ->
                          fun uu____27013  ->
                            fun uu____27014  ->
                              match (uu____27012, uu____27013, uu____27014)
                              with
                              | ((a1,uu____27058),(a2,uu____27060),(is_sub_probs,wl2))
                                  ->
                                  let uu____27093 = is_uvar1 a1  in
                                  if uu____27093
                                  then
                                    ((let uu____27103 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27103
                                      then
                                        let uu____27108 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27110 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27108 uu____27110
                                      else ());
                                     (let uu____27115 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27115 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26913 with
                   | (is_sub_probs,wl2) ->
                       let uu____27143 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27143 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27151 =
                              let uu____27156 =
                                let uu____27157 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27157
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27156
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27151 with
                             | (uu____27164,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27175 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27177 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27175 s uu____27177
                                    in
                                 let uu____27180 =
                                   let uu____27209 =
                                     let uu____27210 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27210.FStar_Syntax_Syntax.n  in
                                   match uu____27209 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27270 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27270 with
                                        | (a::bs1,c3) ->
                                            let uu____27326 =
                                              let uu____27345 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27345
                                                (fun uu____27449  ->
                                                   match uu____27449 with
                                                   | (l1,l2) ->
                                                       let uu____27522 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27522))
                                               in
                                            (match uu____27326 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27627 ->
                                       let uu____27628 =
                                         let uu____27634 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27634)
                                          in
                                       FStar_Errors.raise_error uu____27628 r
                                    in
                                 (match uu____27180 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27710 =
                                        let uu____27717 =
                                          let uu____27718 =
                                            let uu____27719 =
                                              let uu____27726 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27726,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27719
                                             in
                                          [uu____27718]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27717
                                          (fun b  ->
                                             let uu____27742 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27744 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27746 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27742 uu____27744
                                               uu____27746) r
                                         in
                                      (match uu____27710 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27756 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27756
                                             then
                                               let uu____27761 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27770 =
                                                          let uu____27772 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27772
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27770) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27761
                                             else ());
                                            (let wl4 =
                                               let uu___3597_27780 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3597_27780.attempting);
                                                 wl_deferred =
                                                   (uu___3597_27780.wl_deferred);
                                                 ctr = (uu___3597_27780.ctr);
                                                 defer_ok =
                                                   (uu___3597_27780.defer_ok);
                                                 smt_ok =
                                                   (uu___3597_27780.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3597_27780.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3597_27780.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27805 =
                                                        let uu____27812 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27812, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27805) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27829 =
                                               let f_sort_is =
                                                 let uu____27839 =
                                                   let uu____27840 =
                                                     let uu____27843 =
                                                       let uu____27844 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27844.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27843
                                                      in
                                                   uu____27840.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27839 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27855,uu____27856::is)
                                                     ->
                                                     let uu____27898 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____27898
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____27931 ->
                                                     let uu____27932 =
                                                       let uu____27938 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____27938)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____27932 r
                                                  in
                                               let uu____27944 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____27979  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____27979
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28000 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28000
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____27944
                                                in
                                             match uu____27829 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28025 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28025
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28026 =
                                                   let g_sort_is =
                                                     let uu____28036 =
                                                       let uu____28037 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28037.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28036 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28042,uu____28043::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28103 ->
                                                         let uu____28104 =
                                                           let uu____28110 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28110)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28104 r
                                                      in
                                                   let uu____28116 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28151  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28151
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28172
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28172
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28116
                                                    in
                                                 (match uu____28026 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28199 =
                                                          let uu____28204 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28205 =
                                                            let uu____28206 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28206
                                                             in
                                                          (uu____28204,
                                                            uu____28205)
                                                           in
                                                        match uu____28199
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28234 =
                                                          let uu____28237 =
                                                            let uu____28240 =
                                                              let uu____28243
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28243
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28240
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28237
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28234
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28267 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28267
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
                                                        let uu____28278 =
                                                          let uu____28281 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28284  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28284)
                                                            uu____28281
                                                           in
                                                        solve_prob orig
                                                          uu____28278 [] wl6
                                                         in
                                                      let uu____28285 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28285))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28308 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28310 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28310]
              | x -> x  in
            let c12 =
              let uu___3663_28313 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3663_28313.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3663_28313.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3663_28313.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3663_28313.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28314 =
              let uu____28319 =
                FStar_All.pipe_right
                  (let uu___3666_28321 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3666_28321.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3666_28321.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3666_28321.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3666_28321.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28319
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28314
              (fun uu____28335  ->
                 match uu____28335 with
                 | (c,g) ->
                     let uu____28342 =
                       let uu____28344 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28344  in
                     if uu____28342
                     then
                       let uu____28347 =
                         let uu____28353 =
                           let uu____28355 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28357 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28355 uu____28357
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28353)
                          in
                       FStar_Errors.raise_error uu____28347 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28363 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28363
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28369 = lift_c1 ()  in
               solve_eq uu____28369 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28378  ->
                         match uu___31_28378 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28383 -> false))
                  in
               let uu____28385 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28415)::uu____28416,(wp2,uu____28418)::uu____28419)
                     -> (wp1, wp2)
                 | uu____28492 ->
                     let uu____28517 =
                       let uu____28523 =
                         let uu____28525 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28527 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28525 uu____28527
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28523)
                        in
                     FStar_Errors.raise_error uu____28517
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28385 with
               | (wpc1,wpc2) ->
                   let uu____28537 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28537
                   then
                     let uu____28540 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28540 wl
                   else
                     (let uu____28544 =
                        let uu____28551 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28551  in
                      match uu____28544 with
                      | (c2_decl,qualifiers) ->
                          let uu____28572 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28572
                          then
                            let c1_repr =
                              let uu____28579 =
                                let uu____28580 =
                                  let uu____28581 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28581  in
                                let uu____28582 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28580 uu____28582
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28579
                               in
                            let c2_repr =
                              let uu____28585 =
                                let uu____28586 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28587 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28586 uu____28587
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28585
                               in
                            let uu____28589 =
                              let uu____28594 =
                                let uu____28596 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28598 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28596
                                  uu____28598
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28594
                               in
                            (match uu____28589 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28604 = attempt [prob] wl2  in
                                 solve env uu____28604)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28624 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28624
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28647 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28647
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
                                        let uu____28657 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28657 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28664 =
                                        let uu____28671 =
                                          let uu____28672 =
                                            let uu____28689 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28692 =
                                              let uu____28703 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28703; wpc1_2]  in
                                            (uu____28689, uu____28692)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28672
                                           in
                                        FStar_Syntax_Syntax.mk uu____28671
                                         in
                                      uu____28664
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
                                     let uu____28752 =
                                       let uu____28759 =
                                         let uu____28760 =
                                           let uu____28777 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28780 =
                                             let uu____28791 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28800 =
                                               let uu____28811 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28811; wpc1_2]  in
                                             uu____28791 :: uu____28800  in
                                           (uu____28777, uu____28780)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28760
                                          in
                                       FStar_Syntax_Syntax.mk uu____28759  in
                                     uu____28752 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28865 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28865
                              then
                                let uu____28870 =
                                  let uu____28872 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28872
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28870
                              else ());
                             (let uu____28876 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28876 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28885 =
                                      let uu____28888 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _28891  ->
                                           FStar_Pervasives_Native.Some
                                             _28891) uu____28888
                                       in
                                    solve_prob orig uu____28885 [] wl1  in
                                  let uu____28892 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28892))))
           in
        let uu____28893 = FStar_Util.physical_equality c1 c2  in
        if uu____28893
        then
          let uu____28896 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28896
        else
          ((let uu____28900 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28900
            then
              let uu____28905 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28907 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28905
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28907
            else ());
           (let uu____28912 =
              let uu____28921 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28924 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28921, uu____28924)  in
            match uu____28912 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28942),FStar_Syntax_Syntax.Total
                    (t2,uu____28944)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____28961 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28961 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28963,FStar_Syntax_Syntax.Total uu____28964) ->
                     let uu____28981 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____28981 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28985),FStar_Syntax_Syntax.Total
                    (t2,uu____28987)) ->
                     let uu____29004 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29004 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29007),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29009)) ->
                     let uu____29026 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29026 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29029),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29031)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29048 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29048 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29051),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29053)) ->
                     let uu____29070 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29070 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29073,FStar_Syntax_Syntax.Comp uu____29074) ->
                     let uu____29083 =
                       let uu___3790_29086 = problem  in
                       let uu____29089 =
                         let uu____29090 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29090
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3790_29086.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29089;
                         FStar_TypeChecker_Common.relation =
                           (uu___3790_29086.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3790_29086.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3790_29086.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3790_29086.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3790_29086.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3790_29086.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3790_29086.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3790_29086.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29083 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29091,FStar_Syntax_Syntax.Comp uu____29092) ->
                     let uu____29101 =
                       let uu___3790_29104 = problem  in
                       let uu____29107 =
                         let uu____29108 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29108
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3790_29104.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29107;
                         FStar_TypeChecker_Common.relation =
                           (uu___3790_29104.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3790_29104.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3790_29104.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3790_29104.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3790_29104.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3790_29104.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3790_29104.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3790_29104.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29101 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29109,FStar_Syntax_Syntax.GTotal uu____29110) ->
                     let uu____29119 =
                       let uu___3802_29122 = problem  in
                       let uu____29125 =
                         let uu____29126 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29126
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3802_29122.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3802_29122.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3802_29122.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29125;
                         FStar_TypeChecker_Common.element =
                           (uu___3802_29122.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3802_29122.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3802_29122.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3802_29122.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3802_29122.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3802_29122.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29119 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29127,FStar_Syntax_Syntax.Total uu____29128) ->
                     let uu____29137 =
                       let uu___3802_29140 = problem  in
                       let uu____29143 =
                         let uu____29144 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29144
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3802_29140.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3802_29140.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3802_29140.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29143;
                         FStar_TypeChecker_Common.element =
                           (uu___3802_29140.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3802_29140.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3802_29140.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3802_29140.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3802_29140.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3802_29140.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29137 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29145,FStar_Syntax_Syntax.Comp uu____29146) ->
                     let uu____29147 =
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
                     if uu____29147
                     then
                       let uu____29150 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29150 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29157 =
                            let uu____29162 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29162
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29171 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29172 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29171, uu____29172))
                             in
                          match uu____29157 with
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
                           (let uu____29180 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29180
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29188 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29188 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29191 =
                                  FStar_Thunk.mk
                                    (fun uu____29196  ->
                                       let uu____29197 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29199 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29197 uu____29199)
                                   in
                                giveup env uu____29191 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29210 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29210 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29260 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29260 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29285 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29316  ->
                match uu____29316 with
                | (u1,u2) ->
                    let uu____29324 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29326 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29324 uu____29326))
         in
      FStar_All.pipe_right uu____29285 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29363,[])) when
          let uu____29390 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29390 -> "{}"
      | uu____29393 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29420 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29420
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29432 =
              FStar_List.map
                (fun uu____29445  ->
                   match uu____29445 with
                   | (uu____29452,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29432 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29463 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29463 imps
  
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
                  let uu____29520 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29520
                  then
                    let uu____29528 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29530 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29528
                      (rel_to_string rel) uu____29530
                  else "TOP"  in
                let uu____29536 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29536 with
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
              let uu____29596 =
                let uu____29599 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29602  -> FStar_Pervasives_Native.Some _29602)
                  uu____29599
                 in
              FStar_Syntax_Syntax.new_bv uu____29596 t1  in
            let uu____29603 =
              let uu____29608 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29608
               in
            match uu____29603 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29666 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29666
         then
           let uu____29671 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29671
         else ());
        (let uu____29678 =
           FStar_Util.record_time (fun uu____29685  -> solve env probs)  in
         match uu____29678 with
         | (sol,ms) ->
             ((let uu____29697 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29697
               then
                 let uu____29702 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29702
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29715 =
                     FStar_Util.record_time
                       (fun uu____29722  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29715 with
                    | ((),ms1) ->
                        ((let uu____29733 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29733
                          then
                            let uu____29738 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29738
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29750 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29750
                     then
                       let uu____29757 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29757
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
          ((let uu____29783 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29783
            then
              let uu____29788 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29788
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29796 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29796
             then
               let uu____29801 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29801
             else ());
            (let f2 =
               let uu____29807 =
                 let uu____29808 = FStar_Syntax_Util.unmeta f1  in
                 uu____29808.FStar_Syntax_Syntax.n  in
               match uu____29807 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29812 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3919_29813 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3919_29813.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3919_29813.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3919_29813.FStar_TypeChecker_Common.implicits)
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
            let uu____29856 =
              let uu____29857 =
                let uu____29858 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29859  ->
                       FStar_TypeChecker_Common.NonTrivial _29859)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29858;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29857  in
            FStar_All.pipe_left
              (fun _29866  -> FStar_Pervasives_Native.Some _29866)
              uu____29856
  
let with_guard_no_simp :
  'Auu____29876 .
    'Auu____29876 ->
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
            let uu____29916 =
              let uu____29917 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29918  -> FStar_TypeChecker_Common.NonTrivial _29918)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29917;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____29916
  
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
          (let uu____29951 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____29951
           then
             let uu____29956 = FStar_Syntax_Print.term_to_string t1  in
             let uu____29958 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____29956
               uu____29958
           else ());
          (let uu____29963 =
             let uu____29968 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____29968
              in
           match uu____29963 with
           | (prob,wl) ->
               let g =
                 let uu____29976 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____29984  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____29976  in
               ((let uu____30002 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30002
                 then
                   let uu____30007 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30007
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
        let uu____30028 = try_teq true env t1 t2  in
        match uu____30028 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30033 = FStar_TypeChecker_Env.get_range env  in
              let uu____30034 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30033 uu____30034);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30042 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30042
              then
                let uu____30047 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30049 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30051 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30047
                  uu____30049 uu____30051
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
        (let uu____30075 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30075
         then
           let uu____30080 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30082 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30080
             uu____30082
         else ());
        (let uu____30087 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30087 with
         | (prob,x,wl) ->
             let g =
               let uu____30102 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30111  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30102  in
             ((let uu____30129 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30129
               then
                 let uu____30134 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30134
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30142 =
                     let uu____30143 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30143 g1  in
                   FStar_Pervasives_Native.Some uu____30142)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30165 = FStar_TypeChecker_Env.get_range env  in
          let uu____30166 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30165 uu____30166
  
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
        (let uu____30195 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30195
         then
           let uu____30200 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30202 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30200 uu____30202
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30213 =
           let uu____30220 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30220 "sub_comp"
            in
         match uu____30213 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30233 =
                 FStar_Util.record_time
                   (fun uu____30245  ->
                      let uu____30246 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30255  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30246)
                  in
               match uu____30233 with
               | (r,ms) ->
                   ((let uu____30283 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30283
                     then
                       let uu____30288 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30290 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30292 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30288 uu____30290
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30292
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
      fun uu____30330  ->
        match uu____30330 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30373 =
                 let uu____30379 =
                   let uu____30381 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30383 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30381 uu____30383
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30379)  in
               let uu____30387 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30373 uu____30387)
               in
            let equiv1 v1 v' =
              let uu____30400 =
                let uu____30405 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30406 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30405, uu____30406)  in
              match uu____30400 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30426 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____30457 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30457 with
                      | FStar_Syntax_Syntax.U_unif uu____30464 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30493  ->
                                    match uu____30493 with
                                    | (u,v') ->
                                        let uu____30502 = equiv1 v1 v'  in
                                        if uu____30502
                                        then
                                          let uu____30507 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30507 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____30528 -> []))
               in
            let uu____30533 =
              let wl =
                let uu___4030_30537 = empty_worklist env  in
                {
                  attempting = (uu___4030_30537.attempting);
                  wl_deferred = (uu___4030_30537.wl_deferred);
                  ctr = (uu___4030_30537.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4030_30537.smt_ok);
                  umax_heuristic_ok = (uu___4030_30537.umax_heuristic_ok);
                  tcenv = (uu___4030_30537.tcenv);
                  wl_implicits = (uu___4030_30537.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30556  ->
                      match uu____30556 with
                      | (lb,v1) ->
                          let uu____30563 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30563 with
                           | USolved wl1 -> ()
                           | uu____30566 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30577 =
              match uu____30577 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30589) -> true
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
                      uu____30613,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30615,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30626) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30634,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30643 -> false)
               in
            let uu____30649 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30666  ->
                      match uu____30666 with
                      | (u,v1) ->
                          let uu____30674 = check_ineq (u, v1)  in
                          if uu____30674
                          then true
                          else
                            ((let uu____30682 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30682
                              then
                                let uu____30687 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30689 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30687
                                  uu____30689
                              else ());
                             false)))
               in
            if uu____30649
            then ()
            else
              ((let uu____30699 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30699
                then
                  ((let uu____30705 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30705);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30717 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30717))
                else ());
               (let uu____30730 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30730))
  
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
        let fail1 uu____30803 =
          match uu____30803 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4107_30826 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4107_30826.attempting);
            wl_deferred = (uu___4107_30826.wl_deferred);
            ctr = (uu___4107_30826.ctr);
            defer_ok;
            smt_ok = (uu___4107_30826.smt_ok);
            umax_heuristic_ok = (uu___4107_30826.umax_heuristic_ok);
            tcenv = (uu___4107_30826.tcenv);
            wl_implicits = (uu___4107_30826.wl_implicits)
          }  in
        (let uu____30829 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30829
         then
           let uu____30834 = FStar_Util.string_of_bool defer_ok  in
           let uu____30836 = wl_to_string wl  in
           let uu____30838 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30834 uu____30836 uu____30838
         else ());
        (let g1 =
           let uu____30844 = solve_and_commit env wl fail1  in
           match uu____30844 with
           | FStar_Pervasives_Native.Some
               (uu____30851::uu____30852,uu____30853) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4122_30882 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4122_30882.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4122_30882.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30883 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4127_30892 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4127_30892.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4127_30892.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4127_30892.FStar_TypeChecker_Common.implicits)
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
            let uu___4139_30969 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4139_30969.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4139_30969.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4139_30969.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____30970 =
            let uu____30972 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____30972  in
          if uu____30970
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____30984 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____30985 =
                       let uu____30987 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____30987
                        in
                     FStar_Errors.diag uu____30984 uu____30985)
                  else ();
                  (let vc1 =
                     let uu____30993 =
                       let uu____30997 =
                         let uu____30999 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____30999  in
                       FStar_Pervasives_Native.Some uu____30997  in
                     FStar_Profiling.profile
                       (fun uu____31002  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____30993 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug1
                   then
                     (let uu____31006 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31007 =
                        let uu____31009 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31009
                         in
                      FStar_Errors.diag uu____31006 uu____31007)
                   else ();
                   (let uu____31015 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31015
                      "discharge_guard'" env vc1);
                   (let uu____31017 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31017 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____31026 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31027 =
                                let uu____31029 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31029
                                 in
                              FStar_Errors.diag uu____31026 uu____31027)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____31039 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31040 =
                                let uu____31042 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31042
                                 in
                              FStar_Errors.diag uu____31039 uu____31040)
                           else ();
                           (let vcs =
                              let uu____31056 = FStar_Options.use_tactics ()
                                 in
                              if uu____31056
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31078  ->
                                     (let uu____31080 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____31080);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31124  ->
                                              match uu____31124 with
                                              | (env1,goal,opts) ->
                                                  let uu____31140 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31140, opts)))))
                              else
                                (let uu____31144 =
                                   let uu____31151 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31151)  in
                                 [uu____31144])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31184  ->
                                    match uu____31184 with
                                    | (env1,goal,opts) ->
                                        let uu____31194 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31194 with
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
                                                (let uu____31205 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31206 =
                                                   let uu____31208 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31210 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31208 uu____31210
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31205 uu____31206)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____31217 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31218 =
                                                   let uu____31220 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31220
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31217 uu____31218)
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
      let uu____31238 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31238 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31247 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31247
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31261 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31261 with
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
        let uu____31291 = try_teq false env t1 t2  in
        match uu____31291 with
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
            let uu____31335 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31335 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31348 ->
                     let uu____31361 =
                       let uu____31362 = FStar_Syntax_Subst.compress r  in
                       uu____31362.FStar_Syntax_Syntax.n  in
                     (match uu____31361 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31367) ->
                          unresolved ctx_u'
                      | uu____31384 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31408 = acc  in
            match uu____31408 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____31427 = hd1  in
                     (match uu____31427 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____31438 = unresolved ctx_u  in
                             if uu____31438
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31462 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31462
                                     then
                                       let uu____31466 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31466
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31475 = teq_nosmt env1 t tm
                                          in
                                       match uu____31475 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4252_31485 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4252_31485.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4252_31485.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4252_31485.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4252_31485.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4252_31485.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4252_31485.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4252_31485.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4255_31493 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4255_31493.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4255_31493.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4255_31493.FStar_TypeChecker_Common.imp_range)
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
                                    let uu___4259_31504 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4259_31504.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4259_31504.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4259_31504.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4259_31504.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4259_31504.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4259_31504.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4259_31504.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4259_31504.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4259_31504.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4259_31504.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4259_31504.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4259_31504.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4259_31504.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4259_31504.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4259_31504.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4259_31504.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4259_31504.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4259_31504.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4259_31504.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4259_31504.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4259_31504.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4259_31504.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4259_31504.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4259_31504.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4259_31504.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4259_31504.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4259_31504.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4259_31504.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4259_31504.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4259_31504.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4259_31504.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4259_31504.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4259_31504.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4259_31504.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4259_31504.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4259_31504.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4259_31504.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4259_31504.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4259_31504.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4259_31504.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4259_31504.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4259_31504.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4259_31504.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4259_31504.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4259_31504.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4259_31504.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4264_31509 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4264_31509.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4264_31509.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4264_31509.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4264_31509.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4264_31509.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4264_31509.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4264_31509.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4264_31509.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4264_31509.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4264_31509.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4264_31509.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4264_31509.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4264_31509.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4264_31509.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4264_31509.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4264_31509.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4264_31509.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4264_31509.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4264_31509.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4264_31509.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4264_31509.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4264_31509.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4264_31509.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4264_31509.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4264_31509.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4264_31509.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4264_31509.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4264_31509.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4264_31509.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4264_31509.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4264_31509.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4264_31509.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4264_31509.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4264_31509.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4264_31509.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4264_31509.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4264_31509.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4264_31509.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4264_31509.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4264_31509.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4264_31509.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4264_31509.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4264_31509.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4264_31509.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4264_31509.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4264_31509.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31514 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31514
                                   then
                                     let uu____31519 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31521 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31523 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31525 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31519 uu____31521 uu____31523
                                       reason uu____31525
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4270_31532  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31539 =
                                             let uu____31549 =
                                               let uu____31557 =
                                                 let uu____31559 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31561 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31563 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31559 uu____31561
                                                   uu____31563
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31557, r)
                                                in
                                             [uu____31549]  in
                                           FStar_Errors.add_errors
                                             uu____31539);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31582 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31593  ->
                                               let uu____31594 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31596 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31598 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31594 uu____31596
                                                 reason uu____31598)) env2 g1
                                         true
                                        in
                                     match uu____31582 with
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
          let uu___4282_31606 = g  in
          let uu____31607 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4282_31606.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4282_31606.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4282_31606.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31607
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
        let uu____31647 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31647 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31648 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31648
      | imp::uu____31650 ->
          let uu____31653 =
            let uu____31659 =
              let uu____31661 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31663 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31661 uu____31663
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31659)
             in
          FStar_Errors.raise_error uu____31653
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31683 = teq env t1 t2  in
        force_trivial_guard env uu____31683
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31702 = teq_nosmt env t1 t2  in
        match uu____31702 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4307_31721 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4307_31721.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4307_31721.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4307_31721.FStar_TypeChecker_Common.implicits)
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
        (let uu____31757 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31757
         then
           let uu____31762 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31764 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31762
             uu____31764
         else ());
        (let uu____31769 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31769 with
         | (prob,x,wl) ->
             let g =
               let uu____31788 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31797  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31788  in
             ((let uu____31815 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31815
               then
                 let uu____31820 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31822 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31824 =
                   let uu____31826 = FStar_Util.must g  in
                   guard_to_string env uu____31826  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31820 uu____31822 uu____31824
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
        let uu____31863 = check_subtyping env t1 t2  in
        match uu____31863 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31882 =
              let uu____31883 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31883 g  in
            FStar_Pervasives_Native.Some uu____31882
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31902 = check_subtyping env t1 t2  in
        match uu____31902 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31921 =
              let uu____31922 =
                let uu____31923 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31923]  in
              FStar_TypeChecker_Env.close_guard env uu____31922 g  in
            FStar_Pervasives_Native.Some uu____31921
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____31961 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31961
         then
           let uu____31966 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31968 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____31966
             uu____31968
         else ());
        (let uu____31973 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31973 with
         | (prob,x,wl) ->
             let g =
               let uu____31988 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____31997  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31988  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32018 =
                      let uu____32019 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32019]  in
                    FStar_TypeChecker_Env.close_guard env uu____32018 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32060 = subtype_nosmt env t1 t2  in
        match uu____32060 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  