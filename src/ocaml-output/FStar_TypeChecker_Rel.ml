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
              let uu____4012 =
                let uu____4014 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4016 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4014 uu____4016
                 in
              failwith uu____4012
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4031 =
                let uu____4033 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4035 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4033 uu____4035
                 in
              failwith uu____4031
           in
        let uu____4050 = whnf env t1  in aux false uu____4050
  
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
      let uu____4095 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4095 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4136 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4136, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4163 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4163 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4223  ->
    match uu____4223 with
    | (t_base,refopt) ->
        let uu____4254 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4254 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4296 =
      let uu____4300 =
        let uu____4303 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4328  ->
                  match uu____4328 with | (uu____4336,uu____4337,x) -> x))
           in
        FStar_List.append wl.attempting uu____4303  in
      FStar_List.map (wl_prob_to_string wl) uu____4300  in
    FStar_All.pipe_right uu____4296 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____4358 .
    ('Auu____4358 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4370  ->
    match uu____4370 with
    | (uu____4377,c,args) ->
        let uu____4380 = print_ctx_uvar c  in
        let uu____4382 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4380 uu____4382
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4392 = FStar_Syntax_Util.head_and_args t  in
    match uu____4392 with
    | (head1,_args) ->
        let uu____4436 =
          let uu____4437 = FStar_Syntax_Subst.compress head1  in
          uu____4437.FStar_Syntax_Syntax.n  in
        (match uu____4436 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4441 -> true
         | uu____4455 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4463 = FStar_Syntax_Util.head_and_args t  in
    match uu____4463 with
    | (head1,_args) ->
        let uu____4506 =
          let uu____4507 = FStar_Syntax_Subst.compress head1  in
          uu____4507.FStar_Syntax_Syntax.n  in
        (match uu____4506 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4511) -> u
         | uu____4528 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4553 = FStar_Syntax_Util.head_and_args t  in
      match uu____4553 with
      | (head1,args) ->
          let uu____4600 =
            let uu____4601 = FStar_Syntax_Subst.compress head1  in
            uu____4601.FStar_Syntax_Syntax.n  in
          (match uu____4600 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4609)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4642 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_4667  ->
                         match uu___18_4667 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4672 =
                               let uu____4673 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4673.FStar_Syntax_Syntax.n  in
                             (match uu____4672 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4678 -> false)
                         | uu____4680 -> true))
                  in
               (match uu____4642 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4705 =
                        FStar_List.collect
                          (fun uu___19_4717  ->
                             match uu___19_4717 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4721 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4721]
                             | uu____4722 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4705 FStar_List.rev  in
                    let uu____4745 =
                      let uu____4752 =
                        let uu____4761 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_4783  ->
                                  match uu___20_4783 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4787 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4787]
                                  | uu____4788 -> []))
                           in
                        FStar_All.pipe_right uu____4761 FStar_List.rev  in
                      let uu____4811 =
                        let uu____4814 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4814  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4752 uu____4811
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____4745 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4850  ->
                                match uu____4850 with
                                | (x,i) ->
                                    let uu____4869 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4869, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4900  ->
                                match uu____4900 with
                                | (a,i) ->
                                    let uu____4919 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4919, i)) args_sol
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
           | uu____4941 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4963 =
          let uu____4986 =
            let uu____4987 = FStar_Syntax_Subst.compress k  in
            uu____4987.FStar_Syntax_Syntax.n  in
          match uu____4986 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5069 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5069)
              else
                (let uu____5104 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5104 with
                 | (ys',t1,uu____5137) ->
                     let uu____5142 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5142))
          | uu____5181 ->
              let uu____5182 =
                let uu____5187 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5187)  in
              ((ys, t), uu____5182)
           in
        match uu____4963 with
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
                 let uu____5282 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5282 c  in
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
               (let uu____5360 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5360
                then
                  let uu____5365 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5367 = print_ctx_uvar uv  in
                  let uu____5369 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5365 uu____5367 uu____5369
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5378 =
                   let uu____5380 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5380  in
                 let uu____5383 =
                   let uu____5386 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5386
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5378 uu____5383 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5419 =
               let uu____5420 =
                 let uu____5422 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5424 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5422 uu____5424
                  in
               failwith uu____5420  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5490  ->
                       match uu____5490 with
                       | (a,i) ->
                           let uu____5511 =
                             let uu____5512 = FStar_Syntax_Subst.compress a
                                in
                             uu____5512.FStar_Syntax_Syntax.n  in
                           (match uu____5511 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5538 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5548 =
                 let uu____5550 = is_flex g  in Prims.op_Negation uu____5550
                  in
               if uu____5548
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5559 = destruct_flex_t g wl  in
                  match uu____5559 with
                  | ((uu____5564,uv1,args),wl1) ->
                      ((let uu____5569 = args_as_binders args  in
                        assign_solution uu____5569 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___711_5571 = wl1  in
              {
                attempting = (uu___711_5571.attempting);
                wl_deferred = (uu___711_5571.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___711_5571.defer_ok);
                smt_ok = (uu___711_5571.smt_ok);
                umax_heuristic_ok = (uu___711_5571.umax_heuristic_ok);
                tcenv = (uu___711_5571.tcenv);
                wl_implicits = (uu___711_5571.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5596 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5596
         then
           let uu____5601 = FStar_Util.string_of_int pid  in
           let uu____5603 =
             let uu____5605 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5605 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5601 uu____5603
         else ());
        commit sol;
        (let uu___719_5619 = wl  in
         {
           attempting = (uu___719_5619.attempting);
           wl_deferred = (uu___719_5619.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___719_5619.defer_ok);
           smt_ok = (uu___719_5619.smt_ok);
           umax_heuristic_ok = (uu___719_5619.umax_heuristic_ok);
           tcenv = (uu___719_5619.tcenv);
           wl_implicits = (uu___719_5619.wl_implicits)
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
          (let uu____5655 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____5655
           then
             let uu____5660 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____5664 =
               let uu____5666 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____5666 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5660 uu____5664
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
        let uu____5701 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5701 FStar_Util.set_elements  in
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
      let uu____5741 = occurs uk t  in
      match uu____5741 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5780 =
                 let uu____5782 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5784 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5782 uu____5784
                  in
               FStar_Pervasives_Native.Some uu____5780)
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
            let uu____5904 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5904 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5955 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6012  ->
             match uu____6012 with
             | (x,uu____6024) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6042 = FStar_List.last bs  in
      match uu____6042 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6066) ->
          let uu____6077 =
            FStar_Util.prefix_until
              (fun uu___21_6092  ->
                 match uu___21_6092 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6095 -> false) g
             in
          (match uu____6077 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6109,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6146 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6146 with
        | (pfx,uu____6156) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6168 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6168 with
             | (uu____6176,src',wl1) ->
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
                 | uu____6290 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6291 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6355  ->
                  fun uu____6356  ->
                    match (uu____6355, uu____6356) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6459 =
                          let uu____6461 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6461
                           in
                        if uu____6459
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6495 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6495
                           then
                             let uu____6512 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6512)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6291 with | (isect,uu____6562) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6598 'Auu____6599 .
    (FStar_Syntax_Syntax.bv * 'Auu____6598) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6599) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6657  ->
              fun uu____6658  ->
                match (uu____6657, uu____6658) with
                | ((a,uu____6677),(b,uu____6679)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6695 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6695) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6726  ->
           match uu____6726 with
           | (y,uu____6733) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6743 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6743) Prims.list ->
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
                   let uu____6905 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6905
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6938 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6990 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7034 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7055 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7063  ->
    match uu___22_7063 with
    | MisMatch (d1,d2) ->
        let uu____7075 =
          let uu____7077 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7079 =
            let uu____7081 =
              let uu____7083 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7083 ")"  in
            Prims.op_Hat ") (" uu____7081  in
          Prims.op_Hat uu____7077 uu____7079  in
        Prims.op_Hat "MisMatch (" uu____7075
    | HeadMatch u ->
        let uu____7090 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7090
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7099  ->
    match uu___23_7099 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7116 -> HeadMatch false
  
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
          let uu____7138 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7138 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7149 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7173 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7183 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7210 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7210
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7211 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7212 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7213 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7226 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7240 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7264) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7270,uu____7271) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7313) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7338;
             FStar_Syntax_Syntax.index = uu____7339;
             FStar_Syntax_Syntax.sort = t2;_},uu____7341)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7349 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7350 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7351 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7366 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7373 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7393 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7393
  
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
           { FStar_Syntax_Syntax.blob = uu____7412;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7413;
             FStar_Syntax_Syntax.ltyp = uu____7414;
             FStar_Syntax_Syntax.rng = uu____7415;_},uu____7416)
            ->
            let uu____7427 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7427 t21
        | (uu____7428,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7429;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7430;
             FStar_Syntax_Syntax.ltyp = uu____7431;
             FStar_Syntax_Syntax.rng = uu____7432;_})
            ->
            let uu____7443 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7443
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7455 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7455
            then FullMatch
            else
              (let uu____7460 =
                 let uu____7469 =
                   let uu____7472 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7472  in
                 let uu____7473 =
                   let uu____7476 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7476  in
                 (uu____7469, uu____7473)  in
               MisMatch uu____7460)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7482),FStar_Syntax_Syntax.Tm_uinst (g,uu____7484)) ->
            let uu____7493 = head_matches env f g  in
            FStar_All.pipe_right uu____7493 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7494) -> HeadMatch true
        | (uu____7496,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7500 = FStar_Const.eq_const c d  in
            if uu____7500
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7510),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7512)) ->
            let uu____7545 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7545
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7555),FStar_Syntax_Syntax.Tm_refine (y,uu____7557)) ->
            let uu____7566 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7566 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7568),uu____7569) ->
            let uu____7574 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7574 head_match
        | (uu____7575,FStar_Syntax_Syntax.Tm_refine (x,uu____7577)) ->
            let uu____7582 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7582 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7583,FStar_Syntax_Syntax.Tm_type
           uu____7584) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7586,FStar_Syntax_Syntax.Tm_arrow uu____7587) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7618),FStar_Syntax_Syntax.Tm_app (head',uu____7620))
            ->
            let uu____7669 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7669 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7671),uu____7672) ->
            let uu____7697 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7697 head_match
        | (uu____7698,FStar_Syntax_Syntax.Tm_app (head1,uu____7700)) ->
            let uu____7725 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7725 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7726,FStar_Syntax_Syntax.Tm_let
           uu____7727) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7755,FStar_Syntax_Syntax.Tm_match uu____7756) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7802,FStar_Syntax_Syntax.Tm_abs
           uu____7803) -> HeadMatch true
        | uu____7841 ->
            let uu____7846 =
              let uu____7855 = delta_depth_of_term env t11  in
              let uu____7858 = delta_depth_of_term env t21  in
              (uu____7855, uu____7858)  in
            MisMatch uu____7846
  
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
              let uu____7927 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7927  in
            (let uu____7929 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7929
             then
               let uu____7934 = FStar_Syntax_Print.term_to_string t  in
               let uu____7936 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7934 uu____7936
             else ());
            (let uu____7941 =
               let uu____7942 = FStar_Syntax_Util.un_uinst head1  in
               uu____7942.FStar_Syntax_Syntax.n  in
             match uu____7941 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7948 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7948 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7962 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7962
                        then
                          let uu____7967 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7967
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7972 ->
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
                      let uu____7990 =
                        let uu____7992 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7992 = FStar_Syntax_Util.Equal  in
                      if uu____7990
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7999 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7999
                          then
                            let uu____8004 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8006 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8004
                              uu____8006
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8011 -> FStar_Pervasives_Native.None)
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
            (let uu____8163 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8163
             then
               let uu____8168 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8170 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8172 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8168
                 uu____8170 uu____8172
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8200 =
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
               match uu____8200 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8248 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8248 with
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
                  uu____8286),uu____8287)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8308 =
                      let uu____8317 = maybe_inline t11  in
                      let uu____8320 = maybe_inline t21  in
                      (uu____8317, uu____8320)  in
                    match uu____8308 with
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
                 (uu____8363,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8364))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8385 =
                      let uu____8394 = maybe_inline t11  in
                      let uu____8397 = maybe_inline t21  in
                      (uu____8394, uu____8397)  in
                    match uu____8385 with
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
             | MisMatch uu____8452 -> fail1 n_delta r t11 t21
             | uu____8461 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8476 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8476
           then
             let uu____8481 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8483 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8485 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8493 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8510 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8510
                    (fun uu____8545  ->
                       match uu____8545 with
                       | (t11,t21) ->
                           let uu____8553 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8555 =
                             let uu____8557 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8557  in
                           Prims.op_Hat uu____8553 uu____8555))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8481 uu____8483 uu____8485 uu____8493
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8574 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8574 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8589  ->
    match uu___24_8589 with
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
      let uu___1208_8638 = p  in
      let uu____8641 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8642 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1208_8638.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8641;
        FStar_TypeChecker_Common.relation =
          (uu___1208_8638.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8642;
        FStar_TypeChecker_Common.element =
          (uu___1208_8638.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1208_8638.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1208_8638.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1208_8638.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1208_8638.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1208_8638.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8657 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8657
            (fun _8662  -> FStar_TypeChecker_Common.TProb _8662)
      | FStar_TypeChecker_Common.CProb uu____8663 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8686 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8686 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8694 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8694 with
           | (lh,lhs_args) ->
               let uu____8741 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8741 with
                | (rh,rhs_args) ->
                    let uu____8788 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8801,FStar_Syntax_Syntax.Tm_uvar uu____8802)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8891 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8918,uu____8919)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8934,FStar_Syntax_Syntax.Tm_uvar uu____8935)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8950,FStar_Syntax_Syntax.Tm_arrow uu____8951)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1259_8981 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1259_8981.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1259_8981.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1259_8981.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1259_8981.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1259_8981.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1259_8981.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1259_8981.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1259_8981.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1259_8981.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8984,FStar_Syntax_Syntax.Tm_type uu____8985)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1259_9001 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1259_9001.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1259_9001.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1259_9001.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1259_9001.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1259_9001.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1259_9001.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1259_9001.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1259_9001.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1259_9001.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9004,FStar_Syntax_Syntax.Tm_uvar uu____9005)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1259_9021 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1259_9021.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1259_9021.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1259_9021.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1259_9021.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1259_9021.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1259_9021.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1259_9021.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1259_9021.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1259_9021.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9024,FStar_Syntax_Syntax.Tm_uvar uu____9025)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9040,uu____9041)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9056,FStar_Syntax_Syntax.Tm_uvar uu____9057)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9072,uu____9073) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8788 with
                     | (rank,tp1) ->
                         let uu____9086 =
                           FStar_All.pipe_right
                             (let uu___1279_9090 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1279_9090.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1279_9090.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1279_9090.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1279_9090.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1279_9090.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1279_9090.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1279_9090.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1279_9090.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1279_9090.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9093  ->
                                FStar_TypeChecker_Common.TProb _9093)
                            in
                         (rank, uu____9086))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9097 =
            FStar_All.pipe_right
              (let uu___1283_9101 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1283_9101.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1283_9101.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1283_9101.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1283_9101.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1283_9101.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1283_9101.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1283_9101.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1283_9101.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1283_9101.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9104  -> FStar_TypeChecker_Common.CProb _9104)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9097)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9164 probs =
      match uu____9164 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9245 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9266 = rank wl.tcenv hd1  in
               (match uu____9266 with
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
                      (let uu____9327 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9332 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9332)
                          in
                       if uu____9327
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
          let uu____9405 = FStar_Syntax_Util.head_and_args t  in
          match uu____9405 with
          | (hd1,uu____9424) ->
              let uu____9449 =
                let uu____9450 = FStar_Syntax_Subst.compress hd1  in
                uu____9450.FStar_Syntax_Syntax.n  in
              (match uu____9449 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9455) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9490  ->
                           match uu____9490 with
                           | (y,uu____9499) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9522  ->
                                       match uu____9522 with
                                       | (x,uu____9531) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9536 -> false)
           in
        let uu____9538 = rank tcenv p  in
        match uu____9538 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9547 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9628 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9647 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9666 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9683 = FStar_Thunk.mkv s  in UFailed uu____9683 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9698 = FStar_Thunk.mk s  in UFailed uu____9698 
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
                        let uu____9750 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9750 with
                        | (k,uu____9758) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9771 -> false)))
            | uu____9773 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9825 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9833 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9833 = Prims.int_zero))
                           in
                        if uu____9825 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9854 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9862 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9862 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9854)
               in
            let uu____9866 = filter1 u12  in
            let uu____9869 = filter1 u22  in (uu____9866, uu____9869)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9904 = filter_out_common_univs us1 us2  in
                   (match uu____9904 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9964 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9964 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9967 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9984  ->
                               let uu____9985 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____9987 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9985 uu____9987))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10013 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10013 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10039 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10039 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10042 ->
                   ufailed_thunk
                     (fun uu____10053  ->
                        let uu____10054 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10056 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10054 uu____10056 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10059,uu____10060) ->
              let uu____10062 =
                let uu____10064 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10066 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10064 uu____10066
                 in
              failwith uu____10062
          | (FStar_Syntax_Syntax.U_unknown ,uu____10069) ->
              let uu____10070 =
                let uu____10072 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10074 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10072 uu____10074
                 in
              failwith uu____10070
          | (uu____10077,FStar_Syntax_Syntax.U_bvar uu____10078) ->
              let uu____10080 =
                let uu____10082 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10084 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10082 uu____10084
                 in
              failwith uu____10080
          | (uu____10087,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10088 =
                let uu____10090 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10092 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10090 uu____10092
                 in
              failwith uu____10088
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10122 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10122
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10139 = occurs_univ v1 u3  in
              if uu____10139
              then
                let uu____10142 =
                  let uu____10144 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10146 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10144 uu____10146
                   in
                try_umax_components u11 u21 uu____10142
              else
                (let uu____10151 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10151)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10163 = occurs_univ v1 u3  in
              if uu____10163
              then
                let uu____10166 =
                  let uu____10168 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10170 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10168 uu____10170
                   in
                try_umax_components u11 u21 uu____10166
              else
                (let uu____10175 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10175)
          | (FStar_Syntax_Syntax.U_max uu____10176,uu____10177) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10185 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10185
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10191,FStar_Syntax_Syntax.U_max uu____10192) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10200 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10200
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10206,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10208,FStar_Syntax_Syntax.U_name uu____10209) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10211) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10213) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10215,FStar_Syntax_Syntax.U_succ uu____10216) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10218,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10325 = bc1  in
      match uu____10325 with
      | (bs1,mk_cod1) ->
          let uu____10369 = bc2  in
          (match uu____10369 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10480 = aux xs ys  in
                     (match uu____10480 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10563 =
                       let uu____10570 = mk_cod1 xs  in ([], uu____10570)  in
                     let uu____10573 =
                       let uu____10580 = mk_cod2 ys  in ([], uu____10580)  in
                     (uu____10563, uu____10573)
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
                  let uu____10649 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10649 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10652 =
                    let uu____10653 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10653 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10652
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10658 = has_type_guard t1 t2  in (uu____10658, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10659 = has_type_guard t2 t1  in (uu____10659, wl)
  
let is_flex_pat :
  'Auu____10669 'Auu____10670 'Auu____10671 .
    ('Auu____10669 * 'Auu____10670 * 'Auu____10671 Prims.list) -> Prims.bool
  =
  fun uu___25_10685  ->
    match uu___25_10685 with
    | (uu____10694,uu____10695,[]) -> true
    | uu____10699 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10732 = f  in
      match uu____10732 with
      | (uu____10739,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10740;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10741;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10744;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10745;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10746;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10747;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10817  ->
                 match uu____10817 with
                 | (y,uu____10826) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10980 =
                  let uu____10995 =
                    let uu____10998 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10998  in
                  ((FStar_List.rev pat_binders), uu____10995)  in
                FStar_Pervasives_Native.Some uu____10980
            | (uu____11031,[]) ->
                let uu____11062 =
                  let uu____11077 =
                    let uu____11080 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11080  in
                  ((FStar_List.rev pat_binders), uu____11077)  in
                FStar_Pervasives_Native.Some uu____11062
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11171 =
                  let uu____11172 = FStar_Syntax_Subst.compress a  in
                  uu____11172.FStar_Syntax_Syntax.n  in
                (match uu____11171 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11192 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11192
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1611_11222 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1611_11222.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1611_11222.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11226 =
                            let uu____11227 =
                              let uu____11234 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11234)  in
                            FStar_Syntax_Syntax.NT uu____11227  in
                          [uu____11226]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1617_11250 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1617_11250.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1617_11250.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11251 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11291 =
                  let uu____11298 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11298  in
                (match uu____11291 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11357 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11382 ->
               let uu____11383 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11383 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11679 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11679
       then
         let uu____11684 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11684
       else ());
      (let uu____11690 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____11690
       then
         let uu____11695 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11695
       else ());
      (let uu____11700 = next_prob probs  in
       match uu____11700 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1644_11727 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1644_11727.wl_deferred);
               ctr = (uu___1644_11727.ctr);
               defer_ok = (uu___1644_11727.defer_ok);
               smt_ok = (uu___1644_11727.smt_ok);
               umax_heuristic_ok = (uu___1644_11727.umax_heuristic_ok);
               tcenv = (uu___1644_11727.tcenv);
               wl_implicits = (uu___1644_11727.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11736 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11736
                 then
                   let uu____11739 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11739
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
                       (let uu____11746 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd1
                            probs1
                           in
                        solve env uu____11746)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1656_11752 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1656_11752.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1656_11752.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1656_11752.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1656_11752.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1656_11752.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1656_11752.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1656_11752.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1656_11752.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1656_11752.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11777 ->
                let uu____11787 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11852  ->
                          match uu____11852 with
                          | (c,uu____11862,uu____11863) -> c < probs.ctr))
                   in
                (match uu____11787 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11911 =
                            let uu____11916 =
                              FStar_List.map
                                (fun uu____11937  ->
                                   match uu____11937 with
                                   | (uu____11953,x,y) ->
                                       let uu____11964 = FStar_Thunk.force x
                                          in
                                       (uu____11964, y)) probs.wl_deferred
                               in
                            (uu____11916, (probs.wl_implicits))  in
                          Success uu____11911
                      | uu____11968 ->
                          let uu____11978 =
                            let uu___1674_11979 = probs  in
                            let uu____11980 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12001  ->
                                      match uu____12001 with
                                      | (uu____12009,uu____12010,y) -> y))
                               in
                            {
                              attempting = uu____11980;
                              wl_deferred = rest;
                              ctr = (uu___1674_11979.ctr);
                              defer_ok = (uu___1674_11979.defer_ok);
                              smt_ok = (uu___1674_11979.smt_ok);
                              umax_heuristic_ok =
                                (uu___1674_11979.umax_heuristic_ok);
                              tcenv = (uu___1674_11979.tcenv);
                              wl_implicits = (uu___1674_11979.wl_implicits)
                            }  in
                          solve env uu____11978))))

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
            let uu____12019 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12019 with
            | USolved wl1 ->
                let uu____12021 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12021
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12024 = defer_lit "" orig wl1  in
                solve env uu____12024

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
                  let uu____12075 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12075 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12078 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12091;
                  FStar_Syntax_Syntax.vars = uu____12092;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12095;
                  FStar_Syntax_Syntax.vars = uu____12096;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12109,uu____12110) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12118,FStar_Syntax_Syntax.Tm_uinst uu____12119) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12127 -> USolved wl

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
            ((let uu____12138 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12138
              then
                let uu____12143 = prob_to_string env orig  in
                let uu____12145 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12143 uu____12145
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
               let uu____12238 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12238 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12293 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12293
                then
                  let uu____12298 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12300 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12298 uu____12300
                else ());
               (let uu____12305 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12305 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12351 = eq_prob t1 t2 wl2  in
                         (match uu____12351 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12372 ->
                         let uu____12381 = eq_prob t1 t2 wl2  in
                         (match uu____12381 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12431 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12446 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12447 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12446, uu____12447)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12452 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12453 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12452, uu____12453)
                            in
                         (match uu____12431 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12484 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12484 with
                                | (t1_hd,t1_args) ->
                                    let uu____12529 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12529 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12595 =
                                              let uu____12602 =
                                                let uu____12613 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12613 :: t1_args  in
                                              let uu____12630 =
                                                let uu____12639 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12639 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12688  ->
                                                   fun uu____12689  ->
                                                     fun uu____12690  ->
                                                       match (uu____12688,
                                                               uu____12689,
                                                               uu____12690)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12740),
                                                          (a2,uu____12742))
                                                           ->
                                                           let uu____12779 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12779
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12602
                                                uu____12630
                                               in
                                            match uu____12595 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1828_12805 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1828_12805.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1828_12805.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1828_12805.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12816 =
                                                  solve env1 wl'  in
                                                (match uu____12816 with
                                                 | Success (uu____12819,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1837_12823
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1837_12823.attempting);
                                                            wl_deferred =
                                                              (uu___1837_12823.wl_deferred);
                                                            ctr =
                                                              (uu___1837_12823.ctr);
                                                            defer_ok =
                                                              (uu___1837_12823.defer_ok);
                                                            smt_ok =
                                                              (uu___1837_12823.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1837_12823.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1837_12823.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12824 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12856 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12856 with
                                | (t1_base,p1_opt) ->
                                    let uu____12892 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12892 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____12991 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____12991
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
                                               let uu____13044 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13044
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
                                               let uu____13076 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13076
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
                                               let uu____13108 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13108
                                           | uu____13111 -> t_base  in
                                         let uu____13128 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13128 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13142 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13142, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13149 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13149 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13185 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13185 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13221 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13221
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
                              let uu____13245 = combine t11 t21 wl2  in
                              (match uu____13245 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13278 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13278
                                     then
                                       let uu____13283 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13283
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13325 ts1 =
               match uu____13325 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13388 = pairwise out t wl2  in
                        (match uu____13388 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13424 =
               let uu____13435 = FStar_List.hd ts  in (uu____13435, [], wl1)
                in
             let uu____13444 = FStar_List.tl ts  in
             aux uu____13424 uu____13444  in
           let uu____13451 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13451 with
           | (this_flex,this_rigid) ->
               let uu____13477 =
                 let uu____13478 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13478.FStar_Syntax_Syntax.n  in
               (match uu____13477 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13503 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13503
                    then
                      let uu____13506 = destruct_flex_t this_flex wl  in
                      (match uu____13506 with
                       | (flex,wl1) ->
                           let uu____13513 = quasi_pattern env flex  in
                           (match uu____13513 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13532 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13532
                                  then
                                    let uu____13537 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13537
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13544 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1939_13547 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1939_13547.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1939_13547.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1939_13547.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1939_13547.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1939_13547.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1939_13547.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1939_13547.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1939_13547.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1939_13547.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13544)
                | uu____13548 ->
                    ((let uu____13550 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13550
                      then
                        let uu____13555 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13555
                      else ());
                     (let uu____13560 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13560 with
                      | (u,_args) ->
                          let uu____13603 =
                            let uu____13604 = FStar_Syntax_Subst.compress u
                               in
                            uu____13604.FStar_Syntax_Syntax.n  in
                          (match uu____13603 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13632 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13632 with
                                 | (u',uu____13651) ->
                                     let uu____13676 =
                                       let uu____13677 = whnf env u'  in
                                       uu____13677.FStar_Syntax_Syntax.n  in
                                     (match uu____13676 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13699 -> false)
                                  in
                               let uu____13701 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13724  ->
                                         match uu___26_13724 with
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
                                              | uu____13738 -> false)
                                         | uu____13742 -> false))
                                  in
                               (match uu____13701 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13757 = whnf env this_rigid
                                         in
                                      let uu____13758 =
                                        FStar_List.collect
                                          (fun uu___27_13764  ->
                                             match uu___27_13764 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13770 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13770]
                                             | uu____13774 -> [])
                                          bounds_probs
                                         in
                                      uu____13757 :: uu____13758  in
                                    let uu____13775 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13775 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13808 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13823 =
                                               let uu____13824 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13824.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13823 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13836 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13836)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13847 -> bound  in
                                           let uu____13848 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13848)  in
                                         (match uu____13808 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13883 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13883
                                                then
                                                  let wl'1 =
                                                    let uu___1999_13889 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___1999_13889.wl_deferred);
                                                      ctr =
                                                        (uu___1999_13889.ctr);
                                                      defer_ok =
                                                        (uu___1999_13889.defer_ok);
                                                      smt_ok =
                                                        (uu___1999_13889.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___1999_13889.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___1999_13889.tcenv);
                                                      wl_implicits =
                                                        (uu___1999_13889.wl_implicits)
                                                    }  in
                                                  let uu____13890 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13890
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13896 =
                                                  solve_t env eq_prob
                                                    (let uu___2004_13898 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2004_13898.wl_deferred);
                                                       ctr =
                                                         (uu___2004_13898.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2004_13898.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2004_13898.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2004_13898.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13896 with
                                                | Success (uu____13900,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2010_13903 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2010_13903.wl_deferred);
                                                        ctr =
                                                          (uu___2010_13903.ctr);
                                                        defer_ok =
                                                          (uu___2010_13903.defer_ok);
                                                        smt_ok =
                                                          (uu___2010_13903.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2010_13903.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2010_13903.tcenv);
                                                        wl_implicits =
                                                          (uu___2010_13903.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2013_13905 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2013_13905.attempting);
                                                        wl_deferred =
                                                          (uu___2013_13905.wl_deferred);
                                                        ctr =
                                                          (uu___2013_13905.ctr);
                                                        defer_ok =
                                                          (uu___2013_13905.defer_ok);
                                                        smt_ok =
                                                          (uu___2013_13905.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2013_13905.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2013_13905.tcenv);
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
                                                    let uu____13921 =
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
                                                    ((let uu____13933 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13933
                                                      then
                                                        let uu____13938 =
                                                          let uu____13940 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13940
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13938
                                                      else ());
                                                     (let uu____13953 =
                                                        let uu____13968 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13968)
                                                         in
                                                      match uu____13953 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____13990))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14016 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14016
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
                                                                  let uu____14036
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14036))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14061 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14061
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
                                                                    let uu____14081
                                                                    =
                                                                    let uu____14086
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14086
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14081
                                                                    [] wl2
                                                                     in
                                                                  let uu____14092
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14092))))
                                                      | uu____14093 ->
                                                          let uu____14108 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14108 p)))))))
                           | uu____14115 when flip ->
                               let uu____14116 =
                                 let uu____14118 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14120 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14118 uu____14120
                                  in
                               failwith uu____14116
                           | uu____14123 ->
                               let uu____14124 =
                                 let uu____14126 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14128 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14126 uu____14128
                                  in
                               failwith uu____14124)))))

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
                      (fun uu____14164  ->
                         match uu____14164 with
                         | (x,i) ->
                             let uu____14183 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14183, i)) bs_lhs
                     in
                  let uu____14186 = lhs  in
                  match uu____14186 with
                  | (uu____14187,u_lhs,uu____14189) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14286 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14296 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14296, univ)
                             in
                          match uu____14286 with
                          | (k,univ) ->
                              let uu____14303 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14303 with
                               | (uu____14320,u,wl3) ->
                                   let uu____14323 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14323, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14349 =
                              let uu____14362 =
                                let uu____14373 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14373 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14424  ->
                                   fun uu____14425  ->
                                     match (uu____14424, uu____14425) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14526 =
                                           let uu____14533 =
                                             let uu____14536 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14536
                                              in
                                           copy_uvar u_lhs [] uu____14533 wl2
                                            in
                                         (match uu____14526 with
                                          | (uu____14565,t_a,wl3) ->
                                              let uu____14568 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14568 with
                                               | (uu____14587,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14362
                                ([], wl1)
                               in
                            (match uu____14349 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2124_14643 = ct  in
                                   let uu____14644 =
                                     let uu____14647 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14647
                                      in
                                   let uu____14662 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2124_14643.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2124_14643.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14644;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14662;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2124_14643.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2127_14680 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2127_14680.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2127_14680.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14683 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14683 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14721 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14721 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14732 =
                                          let uu____14737 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14737)  in
                                        TERM uu____14732  in
                                      let uu____14738 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14738 with
                                       | (sub_prob,wl3) ->
                                           let uu____14752 =
                                             let uu____14753 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14753
                                              in
                                           solve env uu____14752))
                             | (x,imp)::formals2 ->
                                 let uu____14775 =
                                   let uu____14782 =
                                     let uu____14785 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14785
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14782 wl1
                                    in
                                 (match uu____14775 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14806 =
                                          let uu____14809 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14809
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14806 u_x
                                         in
                                      let uu____14810 =
                                        let uu____14813 =
                                          let uu____14816 =
                                            let uu____14817 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14817, imp)  in
                                          [uu____14816]  in
                                        FStar_List.append bs_terms
                                          uu____14813
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14810 formals2 wl2)
                              in
                           let uu____14844 = occurs_check u_lhs arrow1  in
                           (match uu____14844 with
                            | (uu____14857,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14873 =
                                    FStar_Thunk.mk
                                      (fun uu____14877  ->
                                         let uu____14878 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14878)
                                     in
                                  giveup_or_defer env orig wl uu____14873
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
              (let uu____14911 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14911
               then
                 let uu____14916 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14919 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14916 (rel_to_string (p_rel orig)) uu____14919
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15050 = rhs wl1 scope env1 subst1  in
                     (match uu____15050 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15073 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15073
                            then
                              let uu____15078 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15078
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15156 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15156 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2197_15158 = hd1  in
                       let uu____15159 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2197_15158.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2197_15158.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15159
                       }  in
                     let hd21 =
                       let uu___2200_15163 = hd2  in
                       let uu____15164 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2200_15163.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2200_15163.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15164
                       }  in
                     let uu____15167 =
                       let uu____15172 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15172
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15167 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15195 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15195
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15202 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15202 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15274 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15274
                                  in
                               ((let uu____15292 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15292
                                 then
                                   let uu____15297 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15299 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15297
                                     uu____15299
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15334 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15370 = aux wl [] env [] bs1 bs2  in
               match uu____15370 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15429 = attempt sub_probs wl2  in
                   solve env1 uu____15429)

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
            let uu___2238_15449 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2238_15449.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2238_15449.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15461 = try_solve env wl'  in
          match uu____15461 with
          | Success (uu____15462,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2247_15466 = wl  in
                  {
                    attempting = (uu___2247_15466.attempting);
                    wl_deferred = (uu___2247_15466.wl_deferred);
                    ctr = (uu___2247_15466.ctr);
                    defer_ok = (uu___2247_15466.defer_ok);
                    smt_ok = (uu___2247_15466.smt_ok);
                    umax_heuristic_ok = (uu___2247_15466.umax_heuristic_ok);
                    tcenv = (uu___2247_15466.tcenv);
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
        (let uu____15475 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15475 wl)

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
              let uu____15489 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15489 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15523 = lhs1  in
              match uu____15523 with
              | (uu____15526,ctx_u,uu____15528) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15536 ->
                        let uu____15537 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15537 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15586 = quasi_pattern env1 lhs1  in
              match uu____15586 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15620) ->
                  let uu____15625 = lhs1  in
                  (match uu____15625 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15640 = occurs_check ctx_u rhs1  in
                       (match uu____15640 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15691 =
                                let uu____15699 =
                                  let uu____15701 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15701
                                   in
                                FStar_Util.Inl uu____15699  in
                              (uu____15691, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15729 =
                                 let uu____15731 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15731  in
                               if uu____15729
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15758 =
                                    let uu____15766 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15766  in
                                  let uu____15772 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15758, uu____15772)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15816 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15816 with
              | (rhs_hd,args) ->
                  let uu____15859 = FStar_Util.prefix args  in
                  (match uu____15859 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15931 = lhs1  in
                       (match uu____15931 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15935 =
                              let uu____15946 =
                                let uu____15953 =
                                  let uu____15956 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15956
                                   in
                                copy_uvar u_lhs [] uu____15953 wl1  in
                              match uu____15946 with
                              | (uu____15983,t_last_arg,wl2) ->
                                  let uu____15986 =
                                    let uu____15993 =
                                      let uu____15994 =
                                        let uu____16003 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____16003]  in
                                      FStar_List.append bs_lhs uu____15994
                                       in
                                    copy_uvar u_lhs uu____15993 t_res_lhs wl2
                                     in
                                  (match uu____15986 with
                                   | (uu____16038,lhs',wl3) ->
                                       let uu____16041 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16041 with
                                        | (uu____16058,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15935 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16079 =
                                     let uu____16080 =
                                       let uu____16085 =
                                         let uu____16086 =
                                           let uu____16089 =
                                             let uu____16094 =
                                               let uu____16095 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16095]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16094
                                              in
                                           uu____16089
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16086
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16085)  in
                                     TERM uu____16080  in
                                   [uu____16079]  in
                                 let uu____16120 =
                                   let uu____16127 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16127 with
                                   | (p1,wl3) ->
                                       let uu____16147 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16147 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16120 with
                                  | (sub_probs,wl3) ->
                                      let uu____16179 =
                                        let uu____16180 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16180  in
                                      solve env1 uu____16179))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16214 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16214 with
                | (uu____16232,args) ->
                    (match args with | [] -> false | uu____16268 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16287 =
                  let uu____16288 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16288.FStar_Syntax_Syntax.n  in
                match uu____16287 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16292 -> true
                | uu____16308 -> false  in
              let uu____16310 = quasi_pattern env1 lhs1  in
              match uu____16310 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    FStar_Thunk.mk
                      (fun uu____16328  ->
                         let uu____16329 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16329)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16338 = is_app rhs1  in
                  if uu____16338
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16343 = is_arrow rhs1  in
                     if uu____16343
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          FStar_Thunk.mk
                            (fun uu____16355  ->
                               let uu____16356 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16356)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16360 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16360
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16366 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16366
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16371 = lhs  in
                (match uu____16371 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16375 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16375 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16393 =
                              let uu____16397 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16397
                               in
                            FStar_All.pipe_right uu____16393
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16418 = occurs_check ctx_uv rhs1  in
                          (match uu____16418 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16447 =
                                   let uu____16448 =
                                     let uu____16450 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16450
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16448
                                    in
                                 giveup_or_defer env orig wl uu____16447
                               else
                                 (let uu____16458 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16458
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16465 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16465
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         FStar_Thunk.mk
                                           (fun uu____16478  ->
                                              let uu____16479 =
                                                names_to_string1 fvs2  in
                                              let uu____16481 =
                                                names_to_string1 fvs1  in
                                              let uu____16483 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16479 uu____16481
                                                uu____16483)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16495 ->
                          if wl.defer_ok
                          then
                            let uu____16499 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16499
                          else
                            (let uu____16504 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16504 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16530 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16530
                             | (FStar_Util.Inl msg,uu____16532) ->
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
                  let uu____16550 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16550
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16556 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16556
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16578 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16578
                else
                  (let uu____16583 =
                     let uu____16600 = quasi_pattern env lhs  in
                     let uu____16607 = quasi_pattern env rhs  in
                     (uu____16600, uu____16607)  in
                   match uu____16583 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16650 = lhs  in
                       (match uu____16650 with
                        | ({ FStar_Syntax_Syntax.n = uu____16651;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16653;_},u_lhs,uu____16655)
                            ->
                            let uu____16658 = rhs  in
                            (match uu____16658 with
                             | (uu____16659,u_rhs,uu____16661) ->
                                 let uu____16662 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16662
                                 then
                                   let uu____16669 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16669
                                 else
                                   (let uu____16672 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16672 with
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
                                        let uu____16704 =
                                          let uu____16711 =
                                            let uu____16714 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16714
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16711
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16704 with
                                         | (uu____16726,w,wl1) ->
                                             let w_app =
                                               let uu____16732 =
                                                 let uu____16737 =
                                                   FStar_List.map
                                                     (fun uu____16748  ->
                                                        match uu____16748
                                                        with
                                                        | (z,uu____16756) ->
                                                            let uu____16761 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16761) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16737
                                                  in
                                               uu____16732
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16763 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16763
                                               then
                                                 let uu____16768 =
                                                   let uu____16772 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16774 =
                                                     let uu____16778 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16780 =
                                                       let uu____16784 =
                                                         term_to_string w  in
                                                       let uu____16786 =
                                                         let uu____16790 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16799 =
                                                           let uu____16803 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16812 =
                                                             let uu____16816
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16816]
                                                              in
                                                           uu____16803 ::
                                                             uu____16812
                                                            in
                                                         uu____16790 ::
                                                           uu____16799
                                                          in
                                                       uu____16784 ::
                                                         uu____16786
                                                        in
                                                     uu____16778 ::
                                                       uu____16780
                                                      in
                                                   uu____16772 :: uu____16774
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16768
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16833 =
                                                     let uu____16838 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16838)  in
                                                   TERM uu____16833  in
                                                 let uu____16839 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16839
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16847 =
                                                        let uu____16852 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16852)
                                                         in
                                                      TERM uu____16847  in
                                                    [s1; s2])
                                                  in
                                               let uu____16853 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16853))))))
                   | uu____16854 ->
                       let uu____16871 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16871)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16925 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16925
            then
              let uu____16930 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16932 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16934 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16936 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16930 uu____16932 uu____16934 uu____16936
            else ());
           (let uu____16947 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16947 with
            | (head1,args1) ->
                let uu____16990 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____16990 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17060 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17060 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17065 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17065)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17086 =
                         FStar_Thunk.mk
                           (fun uu____17093  ->
                              let uu____17094 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17096 = args_to_string args1  in
                              let uu____17100 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17102 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17094 uu____17096 uu____17100
                                uu____17102)
                          in
                       giveup env1 uu____17086 orig
                     else
                       (let uu____17109 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17114 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17114 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17109
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2503_17118 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2503_17118.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2503_17118.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2503_17118.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2503_17118.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2503_17118.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2503_17118.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2503_17118.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2503_17118.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17128 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17128
                                    else solve env1 wl2))
                        else
                          (let uu____17133 = base_and_refinement env1 t1  in
                           match uu____17133 with
                           | (base1,refinement1) ->
                               let uu____17158 = base_and_refinement env1 t2
                                  in
                               (match uu____17158 with
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
                                           let uu____17323 =
                                             FStar_List.fold_right
                                               (fun uu____17363  ->
                                                  fun uu____17364  ->
                                                    match (uu____17363,
                                                            uu____17364)
                                                    with
                                                    | (((a1,uu____17416),
                                                        (a2,uu____17418)),
                                                       (probs,wl3)) ->
                                                        let uu____17467 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17467
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17323 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17510 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17510
                                                 then
                                                   let uu____17515 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17515
                                                 else ());
                                                (let uu____17521 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17521
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
                                                    (let uu____17548 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17548 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17564 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17564
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17572 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17572))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17597 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17597 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17613 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17613
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17621 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17621)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17649 =
                                           match uu____17649 with
                                           | (prob,reason) ->
                                               ((let uu____17666 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17666
                                                 then
                                                   let uu____17671 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17673 =
                                                     prob_to_string env2 prob
                                                      in
                                                   let uu____17675 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____17671 uu____17673
                                                     uu____17675
                                                 else ());
                                                (let uu____17681 =
                                                   let uu____17690 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17693 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17690, uu____17693)
                                                    in
                                                 match uu____17681 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17706 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17706 with
                                                      | (head1',uu____17724)
                                                          ->
                                                          let uu____17749 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17749
                                                           with
                                                           | (head2',uu____17767)
                                                               ->
                                                               let uu____17792
                                                                 =
                                                                 let uu____17797
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17798
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17797,
                                                                   uu____17798)
                                                                  in
                                                               (match uu____17792
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17800
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17800
                                                                    then
                                                                    let uu____17805
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17807
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17809
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17811
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17805
                                                                    uu____17807
                                                                    uu____17809
                                                                    uu____17811
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17816
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2591_17824
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2591_17824.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2591_17824.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2591_17824.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2591_17824.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2591_17824.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2591_17824.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2591_17824.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2591_17824.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17826
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17826
                                                                    then
                                                                    let uu____17831
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17831
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17836 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17848 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17848 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17856 =
                                             let uu____17857 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17857.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17856 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17862 -> false  in
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
                                          | uu____17865 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17868 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2611_17904 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2611_17904.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2611_17904.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2611_17904.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2611_17904.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2611_17904.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2611_17904.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2611_17904.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2611_17904.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17980 = destruct_flex_t scrutinee wl1  in
             match uu____17980 with
             | ((_t,uv,_args),wl2) ->
                 let uu____17991 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____17991 with
                  | (xs,pat_term,uu____18007,uu____18008) ->
                      let uu____18013 =
                        FStar_List.fold_left
                          (fun uu____18036  ->
                             fun x  ->
                               match uu____18036 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18057 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18057 with
                                    | (uu____18076,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____18013 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18097 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18097 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2651_18114 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2651_18114.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2651_18114.umax_heuristic_ok);
                                    tcenv = (uu___2651_18114.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18125 = solve env1 wl'  in
                                (match uu____18125 with
                                 | Success (uu____18128,imps) ->
                                     let wl'1 =
                                       let uu___2659_18131 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2659_18131.wl_deferred);
                                         ctr = (uu___2659_18131.ctr);
                                         defer_ok =
                                           (uu___2659_18131.defer_ok);
                                         smt_ok = (uu___2659_18131.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2659_18131.umax_heuristic_ok);
                                         tcenv = (uu___2659_18131.tcenv);
                                         wl_implicits =
                                           (uu___2659_18131.wl_implicits)
                                       }  in
                                     let uu____18132 = solve env1 wl'1  in
                                     (match uu____18132 with
                                      | Success (uu____18135,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2667_18139 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2667_18139.attempting);
                                                 wl_deferred =
                                                   (uu___2667_18139.wl_deferred);
                                                 ctr = (uu___2667_18139.ctr);
                                                 defer_ok =
                                                   (uu___2667_18139.defer_ok);
                                                 smt_ok =
                                                   (uu___2667_18139.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2667_18139.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2667_18139.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18140 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18146 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18169 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18169
                 then
                   let uu____18174 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18176 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18174 uu____18176
                 else ());
                (let uu____18181 =
                   let uu____18202 =
                     let uu____18211 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18211)  in
                   let uu____18218 =
                     let uu____18227 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18227)  in
                   (uu____18202, uu____18218)  in
                 match uu____18181 with
                 | ((uu____18257,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18260;
                                   FStar_Syntax_Syntax.vars = uu____18261;_}),
                    (s,t)) ->
                     let uu____18332 =
                       let uu____18334 = is_flex scrutinee  in
                       Prims.op_Negation uu____18334  in
                     if uu____18332
                     then
                       ((let uu____18345 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18345
                         then
                           let uu____18350 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18350
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18369 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18369
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18384 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18384
                           then
                             let uu____18389 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18391 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18389 uu____18391
                           else ());
                          (let pat_discriminates uu___28_18416 =
                             match uu___28_18416 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18432;
                                  FStar_Syntax_Syntax.p = uu____18433;_},FStar_Pervasives_Native.None
                                ,uu____18434) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18448;
                                  FStar_Syntax_Syntax.p = uu____18449;_},FStar_Pervasives_Native.None
                                ,uu____18450) -> true
                             | uu____18477 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18580 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18580 with
                                       | (uu____18582,uu____18583,t') ->
                                           let uu____18601 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18601 with
                                            | (FullMatch ,uu____18613) ->
                                                true
                                            | (HeadMatch
                                               uu____18627,uu____18628) ->
                                                true
                                            | uu____18643 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18680 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18680
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18691 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18691 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18779,uu____18780) ->
                                       branches1
                                   | uu____18925 -> branches  in
                                 let uu____18980 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____18989 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____18989 with
                                        | (p,uu____18993,uu____18994) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19023  -> FStar_Util.Inr _19023)
                                   uu____18980))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19053 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19053 with
                                | (p,uu____19062,e) ->
                                    ((let uu____19081 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19081
                                      then
                                        let uu____19086 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19088 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19086 uu____19088
                                      else ());
                                     (let uu____19093 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19108  -> FStar_Util.Inr _19108)
                                        uu____19093)))))
                 | ((s,t),(uu____19111,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19114;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19115;_}))
                     ->
                     let uu____19184 =
                       let uu____19186 = is_flex scrutinee  in
                       Prims.op_Negation uu____19186  in
                     if uu____19184
                     then
                       ((let uu____19197 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19197
                         then
                           let uu____19202 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19202
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19221 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19221
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19236 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19236
                           then
                             let uu____19241 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19243 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19241 uu____19243
                           else ());
                          (let pat_discriminates uu___28_19268 =
                             match uu___28_19268 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19284;
                                  FStar_Syntax_Syntax.p = uu____19285;_},FStar_Pervasives_Native.None
                                ,uu____19286) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19300;
                                  FStar_Syntax_Syntax.p = uu____19301;_},FStar_Pervasives_Native.None
                                ,uu____19302) -> true
                             | uu____19329 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19432 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19432 with
                                       | (uu____19434,uu____19435,t') ->
                                           let uu____19453 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19453 with
                                            | (FullMatch ,uu____19465) ->
                                                true
                                            | (HeadMatch
                                               uu____19479,uu____19480) ->
                                                true
                                            | uu____19495 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19532 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19532
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19543 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19543 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19631,uu____19632) ->
                                       branches1
                                   | uu____19777 -> branches  in
                                 let uu____19832 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19841 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19841 with
                                        | (p,uu____19845,uu____19846) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19875  -> FStar_Util.Inr _19875)
                                   uu____19832))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19905 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19905 with
                                | (p,uu____19914,e) ->
                                    ((let uu____19933 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19933
                                      then
                                        let uu____19938 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19940 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19938 uu____19940
                                      else ());
                                     (let uu____19945 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19960  -> FStar_Util.Inr _19960)
                                        uu____19945)))))
                 | uu____19961 ->
                     ((let uu____19983 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19983
                       then
                         let uu____19988 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____19990 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____19988 uu____19990
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20036 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20036
            then
              let uu____20041 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20043 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20045 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20047 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20041 uu____20043 uu____20045 uu____20047
            else ());
           (let uu____20052 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20052 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20083,uu____20084) ->
                     let rec may_relate head3 =
                       let uu____20112 =
                         let uu____20113 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20113.FStar_Syntax_Syntax.n  in
                       match uu____20112 with
                       | FStar_Syntax_Syntax.Tm_name uu____20117 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20119 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20144 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20144 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20146 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20149
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20150 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20153,uu____20154) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20196) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20202) ->
                           may_relate t
                       | uu____20207 -> false  in
                     let uu____20209 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20209 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20222 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20222
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20232 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20232
                          then
                            let uu____20235 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20235 with
                             | (guard,wl2) ->
                                 let uu____20242 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20242)
                          else
                            (let uu____20245 =
                               FStar_Thunk.mk
                                 (fun uu____20252  ->
                                    let uu____20253 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20255 =
                                      let uu____20257 =
                                        let uu____20261 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20261
                                          (fun x  ->
                                             let uu____20268 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20268)
                                         in
                                      FStar_Util.dflt "" uu____20257  in
                                    let uu____20273 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20275 =
                                      let uu____20277 =
                                        let uu____20281 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20281
                                          (fun x  ->
                                             let uu____20288 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20288)
                                         in
                                      FStar_Util.dflt "" uu____20277  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20253 uu____20255 uu____20273
                                      uu____20275)
                                in
                             giveup env1 uu____20245 orig))
                 | (HeadMatch (true ),uu____20294) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20309 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20309 with
                        | (guard,wl2) ->
                            let uu____20316 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20316)
                     else
                       (let uu____20319 =
                          FStar_Thunk.mk
                            (fun uu____20324  ->
                               let uu____20325 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20327 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20325 uu____20327)
                           in
                        giveup env1 uu____20319 orig)
                 | (uu____20330,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2842_20344 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2842_20344.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2842_20344.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2842_20344.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2842_20344.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2842_20344.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2842_20344.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2842_20344.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2842_20344.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20371 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20371
          then
            let uu____20374 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20374
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20380 =
                let uu____20383 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20383  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20380 t1);
             (let uu____20402 =
                let uu____20405 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20405  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20402 t2);
             (let uu____20424 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20424
              then
                let uu____20428 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20430 =
                  let uu____20432 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20434 =
                    let uu____20436 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20436  in
                  Prims.op_Hat uu____20432 uu____20434  in
                let uu____20439 =
                  let uu____20441 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20443 =
                    let uu____20445 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20445  in
                  Prims.op_Hat uu____20441 uu____20443  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20428 uu____20430 uu____20439
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20452,uu____20453) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20477,FStar_Syntax_Syntax.Tm_delayed uu____20478) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20502,uu____20503) ->
                  let uu____20530 =
                    let uu___2873_20531 = problem  in
                    let uu____20532 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2873_20531.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20532;
                      FStar_TypeChecker_Common.relation =
                        (uu___2873_20531.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2873_20531.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2873_20531.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2873_20531.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2873_20531.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2873_20531.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2873_20531.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2873_20531.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20530 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20533,uu____20534) ->
                  let uu____20541 =
                    let uu___2879_20542 = problem  in
                    let uu____20543 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2879_20542.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20543;
                      FStar_TypeChecker_Common.relation =
                        (uu___2879_20542.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2879_20542.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2879_20542.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2879_20542.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2879_20542.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2879_20542.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2879_20542.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2879_20542.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20541 wl
              | (uu____20544,FStar_Syntax_Syntax.Tm_ascribed uu____20545) ->
                  let uu____20572 =
                    let uu___2885_20573 = problem  in
                    let uu____20574 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2885_20573.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2885_20573.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2885_20573.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20574;
                      FStar_TypeChecker_Common.element =
                        (uu___2885_20573.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2885_20573.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2885_20573.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2885_20573.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2885_20573.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2885_20573.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20572 wl
              | (uu____20575,FStar_Syntax_Syntax.Tm_meta uu____20576) ->
                  let uu____20583 =
                    let uu___2891_20584 = problem  in
                    let uu____20585 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2891_20584.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2891_20584.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2891_20584.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20585;
                      FStar_TypeChecker_Common.element =
                        (uu___2891_20584.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2891_20584.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2891_20584.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2891_20584.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2891_20584.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2891_20584.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20583 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20587),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20589)) ->
                  let uu____20598 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20598
              | (FStar_Syntax_Syntax.Tm_bvar uu____20599,uu____20600) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20602,FStar_Syntax_Syntax.Tm_bvar uu____20603) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20673 =
                    match uu___29_20673 with
                    | [] -> c
                    | bs ->
                        let uu____20701 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20701
                     in
                  let uu____20712 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20712 with
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
                                    let uu____20861 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20861
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
                  let mk_t t l uu___30_20950 =
                    match uu___30_20950 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____20992 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____20992 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21137 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21138 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21137
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21138 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21140,uu____21141) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21172 -> true
                    | uu____21192 -> false  in
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
                      (let uu____21252 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2993_21260 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2993_21260.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2993_21260.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2993_21260.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2993_21260.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2993_21260.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2993_21260.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2993_21260.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2993_21260.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2993_21260.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2993_21260.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2993_21260.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2993_21260.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2993_21260.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2993_21260.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2993_21260.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2993_21260.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___2993_21260.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2993_21260.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2993_21260.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2993_21260.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2993_21260.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2993_21260.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2993_21260.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2993_21260.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2993_21260.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2993_21260.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2993_21260.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2993_21260.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2993_21260.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2993_21260.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2993_21260.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2993_21260.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2993_21260.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2993_21260.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2993_21260.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___2993_21260.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2993_21260.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2993_21260.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2993_21260.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2993_21260.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2993_21260.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2993_21260.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2993_21260.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2993_21260.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21252 with
                       | (uu____21265,ty,uu____21267) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21276 =
                                 let uu____21277 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21277.FStar_Syntax_Syntax.n  in
                               match uu____21276 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21280 ->
                                   let uu____21287 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21287
                               | uu____21288 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21291 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21291
                             then
                               let uu____21296 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21298 =
                                 let uu____21300 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21300
                                  in
                               let uu____21301 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21296 uu____21298 uu____21301
                             else ());
                            r1))
                     in
                  let uu____21306 =
                    let uu____21323 = maybe_eta t1  in
                    let uu____21330 = maybe_eta t2  in
                    (uu____21323, uu____21330)  in
                  (match uu____21306 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3014_21372 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3014_21372.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3014_21372.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3014_21372.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3014_21372.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3014_21372.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3014_21372.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3014_21372.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3014_21372.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21393 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21393
                       then
                         let uu____21396 = destruct_flex_t not_abs wl  in
                         (match uu____21396 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21413 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21413.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21413.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21413.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21413.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21413.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21413.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21413.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21413.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21416 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21416 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21439 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21439
                       then
                         let uu____21442 = destruct_flex_t not_abs wl  in
                         (match uu____21442 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21459 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21459.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21459.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21459.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21459.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21459.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21459.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21459.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21459.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21462 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21462 orig))
                   | uu____21465 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21483,FStar_Syntax_Syntax.Tm_abs uu____21484) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21515 -> true
                    | uu____21535 -> false  in
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
                      (let uu____21595 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2993_21603 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2993_21603.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2993_21603.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2993_21603.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2993_21603.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2993_21603.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2993_21603.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2993_21603.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2993_21603.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2993_21603.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2993_21603.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2993_21603.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2993_21603.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2993_21603.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2993_21603.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2993_21603.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2993_21603.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___2993_21603.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2993_21603.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2993_21603.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2993_21603.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2993_21603.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2993_21603.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2993_21603.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2993_21603.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2993_21603.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2993_21603.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2993_21603.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2993_21603.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2993_21603.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2993_21603.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2993_21603.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2993_21603.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2993_21603.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2993_21603.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2993_21603.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___2993_21603.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2993_21603.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2993_21603.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2993_21603.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2993_21603.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2993_21603.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2993_21603.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2993_21603.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2993_21603.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21595 with
                       | (uu____21608,ty,uu____21610) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21619 =
                                 let uu____21620 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21620.FStar_Syntax_Syntax.n  in
                               match uu____21619 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21623 ->
                                   let uu____21630 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21630
                               | uu____21631 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21634 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21634
                             then
                               let uu____21639 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21641 =
                                 let uu____21643 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21643
                                  in
                               let uu____21644 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21639 uu____21641 uu____21644
                             else ());
                            r1))
                     in
                  let uu____21649 =
                    let uu____21666 = maybe_eta t1  in
                    let uu____21673 = maybe_eta t2  in
                    (uu____21666, uu____21673)  in
                  (match uu____21649 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3014_21715 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3014_21715.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3014_21715.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3014_21715.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3014_21715.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3014_21715.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3014_21715.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3014_21715.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3014_21715.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21736 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21736
                       then
                         let uu____21739 = destruct_flex_t not_abs wl  in
                         (match uu____21739 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21756 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21756.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21756.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21756.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21756.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21756.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21756.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21756.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21756.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21759 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21759 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21782 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21782
                       then
                         let uu____21785 = destruct_flex_t not_abs wl  in
                         (match uu____21785 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21802 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21802.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21802.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21802.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21802.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21802.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21802.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21802.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21802.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21805 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21805 orig))
                   | uu____21808 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21838 =
                    let uu____21843 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21843 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3054_21871 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3054_21871.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3054_21871.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3056_21873 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3056_21873.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3056_21873.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21874,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3054_21889 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3054_21889.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3054_21889.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3056_21891 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3056_21891.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3056_21891.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21892 -> (x1, x2)  in
                  (match uu____21838 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21911 = as_refinement false env t11  in
                       (match uu____21911 with
                        | (x12,phi11) ->
                            let uu____21919 = as_refinement false env t21  in
                            (match uu____21919 with
                             | (x22,phi21) ->
                                 ((let uu____21928 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21928
                                   then
                                     ((let uu____21933 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21935 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21937 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21933
                                         uu____21935 uu____21937);
                                      (let uu____21940 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21942 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21944 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21940
                                         uu____21942 uu____21944))
                                   else ());
                                  (let uu____21949 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21949 with
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
                                         let uu____22020 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22020
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22032 =
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
                                         (let uu____22045 =
                                            let uu____22048 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22048
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22045
                                            (p_guard base_prob));
                                         (let uu____22067 =
                                            let uu____22070 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22070
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22067
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22089 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22089)
                                          in
                                       let has_uvars =
                                         (let uu____22094 =
                                            let uu____22096 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22096
                                             in
                                          Prims.op_Negation uu____22094) ||
                                           (let uu____22100 =
                                              let uu____22102 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22102
                                               in
                                            Prims.op_Negation uu____22100)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22106 =
                                           let uu____22111 =
                                             let uu____22120 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22120]  in
                                           mk_t_problem wl1 uu____22111 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22106 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22143 =
                                                solve env1
                                                  (let uu___3099_22145 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3099_22145.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3099_22145.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3099_22145.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3099_22145.tcenv);
                                                     wl_implicits =
                                                       (uu___3099_22145.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22143 with
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
                                               | Success uu____22160 ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22169 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22169
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3112_22178 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3112_22178.attempting);
                                                         wl_deferred =
                                                           (uu___3112_22178.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3112_22178.defer_ok);
                                                         smt_ok =
                                                           (uu___3112_22178.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3112_22178.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3112_22178.tcenv);
                                                         wl_implicits =
                                                           (uu___3112_22178.wl_implicits)
                                                       }  in
                                                     let uu____22180 =
                                                       attempt [base_prob]
                                                         wl4
                                                        in
                                                     solve env1 uu____22180))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22183,FStar_Syntax_Syntax.Tm_uvar uu____22184) ->
                  let uu____22209 = destruct_flex_t t1 wl  in
                  (match uu____22209 with
                   | (f1,wl1) ->
                       let uu____22216 = destruct_flex_t t2 wl1  in
                       (match uu____22216 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22223;
                    FStar_Syntax_Syntax.pos = uu____22224;
                    FStar_Syntax_Syntax.vars = uu____22225;_},uu____22226),FStar_Syntax_Syntax.Tm_uvar
                 uu____22227) ->
                  let uu____22276 = destruct_flex_t t1 wl  in
                  (match uu____22276 with
                   | (f1,wl1) ->
                       let uu____22283 = destruct_flex_t t2 wl1  in
                       (match uu____22283 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22290,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22291;
                    FStar_Syntax_Syntax.pos = uu____22292;
                    FStar_Syntax_Syntax.vars = uu____22293;_},uu____22294))
                  ->
                  let uu____22343 = destruct_flex_t t1 wl  in
                  (match uu____22343 with
                   | (f1,wl1) ->
                       let uu____22350 = destruct_flex_t t2 wl1  in
                       (match uu____22350 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22357;
                    FStar_Syntax_Syntax.pos = uu____22358;
                    FStar_Syntax_Syntax.vars = uu____22359;_},uu____22360),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22361;
                    FStar_Syntax_Syntax.pos = uu____22362;
                    FStar_Syntax_Syntax.vars = uu____22363;_},uu____22364))
                  ->
                  let uu____22437 = destruct_flex_t t1 wl  in
                  (match uu____22437 with
                   | (f1,wl1) ->
                       let uu____22444 = destruct_flex_t t2 wl1  in
                       (match uu____22444 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22451,uu____22452) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22465 = destruct_flex_t t1 wl  in
                  (match uu____22465 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22472;
                    FStar_Syntax_Syntax.pos = uu____22473;
                    FStar_Syntax_Syntax.vars = uu____22474;_},uu____22475),uu____22476)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22513 = destruct_flex_t t1 wl  in
                  (match uu____22513 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22520,FStar_Syntax_Syntax.Tm_uvar uu____22521) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22534,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22535;
                    FStar_Syntax_Syntax.pos = uu____22536;
                    FStar_Syntax_Syntax.vars = uu____22537;_},uu____22538))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22575,FStar_Syntax_Syntax.Tm_arrow uu____22576) ->
                  solve_t' env
                    (let uu___3212_22604 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3212_22604.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3212_22604.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3212_22604.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3212_22604.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3212_22604.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3212_22604.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3212_22604.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3212_22604.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3212_22604.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22605;
                    FStar_Syntax_Syntax.pos = uu____22606;
                    FStar_Syntax_Syntax.vars = uu____22607;_},uu____22608),FStar_Syntax_Syntax.Tm_arrow
                 uu____22609) ->
                  solve_t' env
                    (let uu___3212_22661 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3212_22661.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3212_22661.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3212_22661.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3212_22661.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3212_22661.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3212_22661.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3212_22661.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3212_22661.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3212_22661.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22662,FStar_Syntax_Syntax.Tm_uvar uu____22663) ->
                  let uu____22676 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22676
              | (uu____22677,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22678;
                    FStar_Syntax_Syntax.pos = uu____22679;
                    FStar_Syntax_Syntax.vars = uu____22680;_},uu____22681))
                  ->
                  let uu____22718 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22718
              | (FStar_Syntax_Syntax.Tm_uvar uu____22719,uu____22720) ->
                  let uu____22733 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22733
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22734;
                    FStar_Syntax_Syntax.pos = uu____22735;
                    FStar_Syntax_Syntax.vars = uu____22736;_},uu____22737),uu____22738)
                  ->
                  let uu____22775 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22775
              | (FStar_Syntax_Syntax.Tm_refine uu____22776,uu____22777) ->
                  let t21 =
                    let uu____22785 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22785  in
                  solve_t env
                    (let uu___3247_22811 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3247_22811.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3247_22811.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3247_22811.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3247_22811.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3247_22811.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3247_22811.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3247_22811.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3247_22811.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3247_22811.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22812,FStar_Syntax_Syntax.Tm_refine uu____22813) ->
                  let t11 =
                    let uu____22821 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22821  in
                  solve_t env
                    (let uu___3254_22847 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3254_22847.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3254_22847.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3254_22847.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3254_22847.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3254_22847.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3254_22847.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3254_22847.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3254_22847.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3254_22847.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22929 =
                    let uu____22930 = guard_of_prob env wl problem t1 t2  in
                    match uu____22930 with
                    | (guard,wl1) ->
                        let uu____22937 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22937
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23156 = br1  in
                        (match uu____23156 with
                         | (p1,w1,uu____23185) ->
                             let uu____23202 = br2  in
                             (match uu____23202 with
                              | (p2,w2,uu____23225) ->
                                  let uu____23230 =
                                    let uu____23232 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23232  in
                                  if uu____23230
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23259 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23259 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23296 = br2  in
                                         (match uu____23296 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23329 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23329
                                                 in
                                              let uu____23334 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23365,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23386) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23445 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23445 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23334
                                                (fun uu____23517  ->
                                                   match uu____23517 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23554 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23554
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23575
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23575
                                                              then
                                                                let uu____23580
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23582
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23580
                                                                  uu____23582
                                                              else ());
                                                             (let uu____23588
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23588
                                                                (fun
                                                                   uu____23624
                                                                    ->
                                                                   match uu____23624
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
                    | uu____23753 -> FStar_Pervasives_Native.None  in
                  let uu____23794 = solve_branches wl brs1 brs2  in
                  (match uu____23794 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23820 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23820 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23847 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23847 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23881 =
                                FStar_List.map
                                  (fun uu____23893  ->
                                     match uu____23893 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23881  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23902 =
                              let uu____23903 =
                                let uu____23904 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23904
                                  (let uu___3353_23912 = wl3  in
                                   {
                                     attempting =
                                       (uu___3353_23912.attempting);
                                     wl_deferred =
                                       (uu___3353_23912.wl_deferred);
                                     ctr = (uu___3353_23912.ctr);
                                     defer_ok = (uu___3353_23912.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3353_23912.umax_heuristic_ok);
                                     tcenv = (uu___3353_23912.tcenv);
                                     wl_implicits =
                                       (uu___3353_23912.wl_implicits)
                                   })
                                 in
                              solve env uu____23903  in
                            (match uu____23902 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23917 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____23926 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____23926 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____23929,uu____23930) ->
                  let head1 =
                    let uu____23954 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23954
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24000 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24000
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24046 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24046
                    then
                      let uu____24050 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24052 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24054 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24050 uu____24052 uu____24054
                    else ());
                   (let no_free_uvars t =
                      (let uu____24068 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24068) &&
                        (let uu____24072 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24072)
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
                      let uu____24091 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24091 = FStar_Syntax_Util.Equal  in
                    let uu____24092 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24092
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24096 = equal t1 t2  in
                         (if uu____24096
                          then
                            let uu____24099 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24099
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24104 =
                            let uu____24111 = equal t1 t2  in
                            if uu____24111
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24124 = mk_eq2 wl env orig t1 t2  in
                               match uu____24124 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24104 with
                          | (guard,wl1) ->
                              let uu____24145 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24145))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24148,uu____24149) ->
                  let head1 =
                    let uu____24157 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24157
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24203 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24203
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24249 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24249
                    then
                      let uu____24253 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24255 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24257 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24253 uu____24255 uu____24257
                    else ());
                   (let no_free_uvars t =
                      (let uu____24271 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24271) &&
                        (let uu____24275 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24275)
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
                      let uu____24294 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24294 = FStar_Syntax_Util.Equal  in
                    let uu____24295 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24295
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24299 = equal t1 t2  in
                         (if uu____24299
                          then
                            let uu____24302 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24302
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24307 =
                            let uu____24314 = equal t1 t2  in
                            if uu____24314
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24327 = mk_eq2 wl env orig t1 t2  in
                               match uu____24327 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24307 with
                          | (guard,wl1) ->
                              let uu____24348 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24348))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24351,uu____24352) ->
                  let head1 =
                    let uu____24354 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24354
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24400 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24400
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24446 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24446
                    then
                      let uu____24450 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24452 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24454 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24450 uu____24452 uu____24454
                    else ());
                   (let no_free_uvars t =
                      (let uu____24468 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24468) &&
                        (let uu____24472 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24472)
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
                      let uu____24491 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24491 = FStar_Syntax_Util.Equal  in
                    let uu____24492 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24492
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24496 = equal t1 t2  in
                         (if uu____24496
                          then
                            let uu____24499 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24499
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24504 =
                            let uu____24511 = equal t1 t2  in
                            if uu____24511
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24524 = mk_eq2 wl env orig t1 t2  in
                               match uu____24524 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24504 with
                          | (guard,wl1) ->
                              let uu____24545 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24545))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24548,uu____24549) ->
                  let head1 =
                    let uu____24551 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24551
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24597 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24597
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24643 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24643
                    then
                      let uu____24647 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24649 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24651 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24647 uu____24649 uu____24651
                    else ());
                   (let no_free_uvars t =
                      (let uu____24665 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24665) &&
                        (let uu____24669 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24669)
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
                      let uu____24688 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24688 = FStar_Syntax_Util.Equal  in
                    let uu____24689 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24689
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24693 = equal t1 t2  in
                         (if uu____24693
                          then
                            let uu____24696 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24696
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24701 =
                            let uu____24708 = equal t1 t2  in
                            if uu____24708
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24721 = mk_eq2 wl env orig t1 t2  in
                               match uu____24721 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24701 with
                          | (guard,wl1) ->
                              let uu____24742 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24742))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24745,uu____24746) ->
                  let head1 =
                    let uu____24748 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24748
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24794 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24794
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24840 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24840
                    then
                      let uu____24844 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24846 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24848 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24844 uu____24846 uu____24848
                    else ());
                   (let no_free_uvars t =
                      (let uu____24862 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24862) &&
                        (let uu____24866 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24866)
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
                      let uu____24885 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24885 = FStar_Syntax_Util.Equal  in
                    let uu____24886 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24886
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24890 = equal t1 t2  in
                         (if uu____24890
                          then
                            let uu____24893 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24893
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24898 =
                            let uu____24905 = equal t1 t2  in
                            if uu____24905
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24918 = mk_eq2 wl env orig t1 t2  in
                               match uu____24918 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24898 with
                          | (guard,wl1) ->
                              let uu____24939 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24939))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24942,uu____24943) ->
                  let head1 =
                    let uu____24961 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24961
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25007 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25007
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25053 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25053
                    then
                      let uu____25057 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25059 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25061 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25057 uu____25059 uu____25061
                    else ());
                   (let no_free_uvars t =
                      (let uu____25075 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25075) &&
                        (let uu____25079 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25079)
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
                      let uu____25098 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25098 = FStar_Syntax_Util.Equal  in
                    let uu____25099 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25099
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25103 = equal t1 t2  in
                         (if uu____25103
                          then
                            let uu____25106 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25106
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25111 =
                            let uu____25118 = equal t1 t2  in
                            if uu____25118
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25131 = mk_eq2 wl env orig t1 t2  in
                               match uu____25131 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25111 with
                          | (guard,wl1) ->
                              let uu____25152 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25152))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25155,FStar_Syntax_Syntax.Tm_match uu____25156) ->
                  let head1 =
                    let uu____25180 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25180
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25226 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25226
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25272 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25272
                    then
                      let uu____25276 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25278 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25280 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25276 uu____25278 uu____25280
                    else ());
                   (let no_free_uvars t =
                      (let uu____25294 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25294) &&
                        (let uu____25298 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25298)
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
                      let uu____25317 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25317 = FStar_Syntax_Util.Equal  in
                    let uu____25318 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25318
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25322 = equal t1 t2  in
                         (if uu____25322
                          then
                            let uu____25325 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25325
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25330 =
                            let uu____25337 = equal t1 t2  in
                            if uu____25337
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25350 = mk_eq2 wl env orig t1 t2  in
                               match uu____25350 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25330 with
                          | (guard,wl1) ->
                              let uu____25371 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25371))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25374,FStar_Syntax_Syntax.Tm_uinst uu____25375) ->
                  let head1 =
                    let uu____25383 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25383
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25429 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25429
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25475 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25475
                    then
                      let uu____25479 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25481 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25483 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25479 uu____25481 uu____25483
                    else ());
                   (let no_free_uvars t =
                      (let uu____25497 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25497) &&
                        (let uu____25501 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25501)
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
                      let uu____25520 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25520 = FStar_Syntax_Util.Equal  in
                    let uu____25521 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25521
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25525 = equal t1 t2  in
                         (if uu____25525
                          then
                            let uu____25528 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25528
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25533 =
                            let uu____25540 = equal t1 t2  in
                            if uu____25540
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25553 = mk_eq2 wl env orig t1 t2  in
                               match uu____25553 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25533 with
                          | (guard,wl1) ->
                              let uu____25574 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25574))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25577,FStar_Syntax_Syntax.Tm_name uu____25578) ->
                  let head1 =
                    let uu____25580 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25580
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25626 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25626
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25666 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25666
                    then
                      let uu____25670 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25672 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25674 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25670 uu____25672 uu____25674
                    else ());
                   (let no_free_uvars t =
                      (let uu____25688 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25688) &&
                        (let uu____25692 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25692)
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
                      let uu____25711 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25711 = FStar_Syntax_Util.Equal  in
                    let uu____25712 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25712
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25716 = equal t1 t2  in
                         (if uu____25716
                          then
                            let uu____25719 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25719
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25724 =
                            let uu____25731 = equal t1 t2  in
                            if uu____25731
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25744 = mk_eq2 wl env orig t1 t2  in
                               match uu____25744 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25724 with
                          | (guard,wl1) ->
                              let uu____25765 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25765))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25768,FStar_Syntax_Syntax.Tm_constant uu____25769) ->
                  let head1 =
                    let uu____25771 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25771
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25811 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25811
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25851 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25851
                    then
                      let uu____25855 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25857 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25859 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25855 uu____25857 uu____25859
                    else ());
                   (let no_free_uvars t =
                      (let uu____25873 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25873) &&
                        (let uu____25877 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25877)
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
                      let uu____25896 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25896 = FStar_Syntax_Util.Equal  in
                    let uu____25897 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25897
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25901 = equal t1 t2  in
                         (if uu____25901
                          then
                            let uu____25904 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25904
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25909 =
                            let uu____25916 = equal t1 t2  in
                            if uu____25916
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25929 = mk_eq2 wl env orig t1 t2  in
                               match uu____25929 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25909 with
                          | (guard,wl1) ->
                              let uu____25950 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25950))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25953,FStar_Syntax_Syntax.Tm_fvar uu____25954) ->
                  let head1 =
                    let uu____25956 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25956
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26002 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26002
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26048 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26048
                    then
                      let uu____26052 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26054 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26056 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26052 uu____26054 uu____26056
                    else ());
                   (let no_free_uvars t =
                      (let uu____26070 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26070) &&
                        (let uu____26074 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26074)
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
                      let uu____26093 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26093 = FStar_Syntax_Util.Equal  in
                    let uu____26094 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26094
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26098 = equal t1 t2  in
                         (if uu____26098
                          then
                            let uu____26101 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26101
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26106 =
                            let uu____26113 = equal t1 t2  in
                            if uu____26113
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26126 = mk_eq2 wl env orig t1 t2  in
                               match uu____26126 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26106 with
                          | (guard,wl1) ->
                              let uu____26147 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26147))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26150,FStar_Syntax_Syntax.Tm_app uu____26151) ->
                  let head1 =
                    let uu____26169 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26169
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26209 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26209
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26249 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26249
                    then
                      let uu____26253 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26255 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26257 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26253 uu____26255 uu____26257
                    else ());
                   (let no_free_uvars t =
                      (let uu____26271 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26271) &&
                        (let uu____26275 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26275)
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
                      let uu____26294 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26294 = FStar_Syntax_Util.Equal  in
                    let uu____26295 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26295
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26299 = equal t1 t2  in
                         (if uu____26299
                          then
                            let uu____26302 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26302
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26307 =
                            let uu____26314 = equal t1 t2  in
                            if uu____26314
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26327 = mk_eq2 wl env orig t1 t2  in
                               match uu____26327 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26307 with
                          | (guard,wl1) ->
                              let uu____26348 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26348))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26351,FStar_Syntax_Syntax.Tm_let uu____26352) ->
                  let uu____26379 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26379
                  then
                    let uu____26382 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26382
                  else
                    (let uu____26385 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26385 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26388,uu____26389) ->
                  let uu____26403 =
                    let uu____26409 =
                      let uu____26411 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26413 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26415 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26417 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26411 uu____26413 uu____26415 uu____26417
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26409)
                     in
                  FStar_Errors.raise_error uu____26403
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26421,FStar_Syntax_Syntax.Tm_let uu____26422) ->
                  let uu____26436 =
                    let uu____26442 =
                      let uu____26444 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26446 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26448 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26450 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26444 uu____26446 uu____26448 uu____26450
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26442)
                     in
                  FStar_Errors.raise_error uu____26436
                    t1.FStar_Syntax_Syntax.pos
              | uu____26454 ->
                  let uu____26459 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26459 orig))))

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
          (let uu____26525 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26525
           then
             let uu____26530 =
               let uu____26532 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26532  in
             let uu____26533 =
               let uu____26535 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26535  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26530 uu____26533
           else ());
          (let uu____26539 =
             let uu____26541 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26541  in
           if uu____26539
           then
             let uu____26544 =
               FStar_Thunk.mk
                 (fun uu____26549  ->
                    let uu____26550 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26552 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26550 uu____26552)
                in
             giveup env uu____26544 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26574 =
                  FStar_Thunk.mk
                    (fun uu____26579  ->
                       let uu____26580 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26582 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26580 uu____26582)
                   in
                giveup env uu____26574 orig)
             else
               (let uu____26587 =
                  FStar_List.fold_left2
                    (fun uu____26608  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26608 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26629 =
                                 let uu____26634 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26635 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26634
                                   FStar_TypeChecker_Common.EQ uu____26635
                                   "effect universes"
                                  in
                               (match uu____26629 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26587 with
                | (univ_sub_probs,wl1) ->
                    let uu____26655 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26655 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26663 =
                           FStar_List.fold_right2
                             (fun uu____26700  ->
                                fun uu____26701  ->
                                  fun uu____26702  ->
                                    match (uu____26700, uu____26701,
                                            uu____26702)
                                    with
                                    | ((a1,uu____26746),(a2,uu____26748),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26781 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26781 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26663 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26808 =
                                  let uu____26811 =
                                    let uu____26814 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26814
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26811
                                   in
                                FStar_List.append univ_sub_probs uu____26808
                                 in
                              let guard =
                                let guard =
                                  let uu____26836 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26836  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3505_26845 = wl3  in
                                {
                                  attempting = (uu___3505_26845.attempting);
                                  wl_deferred = (uu___3505_26845.wl_deferred);
                                  ctr = (uu___3505_26845.ctr);
                                  defer_ok = (uu___3505_26845.defer_ok);
                                  smt_ok = (uu___3505_26845.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3505_26845.umax_heuristic_ok);
                                  tcenv = (uu___3505_26845.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26847 = attempt sub_probs wl5  in
                              solve env uu____26847))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26865 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26865
           then
             let uu____26870 =
               let uu____26872 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26872
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26874 =
               let uu____26876 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26876
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26870 uu____26874
           else ());
          (let uu____26881 =
             let uu____26886 =
               let uu____26891 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26891
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26886
               (fun uu____26908  ->
                  match uu____26908 with
                  | (c,g) ->
                      let uu____26919 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26919, g))
              in
           match uu____26881 with
           | (c12,g_lift) ->
               ((let uu____26923 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26923
                 then
                   let uu____26928 =
                     let uu____26930 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26930
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26932 =
                     let uu____26934 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26934
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26928 uu____26932
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3525_26944 = wl  in
                     {
                       attempting = (uu___3525_26944.attempting);
                       wl_deferred = (uu___3525_26944.wl_deferred);
                       ctr = (uu___3525_26944.ctr);
                       defer_ok = (uu___3525_26944.defer_ok);
                       smt_ok = (uu___3525_26944.smt_ok);
                       umax_heuristic_ok =
                         (uu___3525_26944.umax_heuristic_ok);
                       tcenv = (uu___3525_26944.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26945 =
                     let rec is_uvar1 t =
                       let uu____26959 =
                         let uu____26960 = FStar_Syntax_Subst.compress t  in
                         uu____26960.FStar_Syntax_Syntax.n  in
                       match uu____26959 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26964 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____26979) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____26985) ->
                           is_uvar1 t1
                       | uu____27010 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27044  ->
                          fun uu____27045  ->
                            fun uu____27046  ->
                              match (uu____27044, uu____27045, uu____27046)
                              with
                              | ((a1,uu____27090),(a2,uu____27092),(is_sub_probs,wl2))
                                  ->
                                  let uu____27125 = is_uvar1 a1  in
                                  if uu____27125
                                  then
                                    ((let uu____27135 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27135
                                      then
                                        let uu____27140 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27142 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27140 uu____27142
                                      else ());
                                     (let uu____27147 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27147 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26945 with
                   | (is_sub_probs,wl2) ->
                       let uu____27175 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27175 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27183 =
                              let uu____27188 =
                                let uu____27189 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27189
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27188
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27183 with
                             | (uu____27196,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27207 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27209 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27207 s uu____27209
                                    in
                                 let uu____27212 =
                                   let uu____27241 =
                                     let uu____27242 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27242.FStar_Syntax_Syntax.n  in
                                   match uu____27241 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27302 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27302 with
                                        | (a::bs1,c3) ->
                                            let uu____27358 =
                                              let uu____27377 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27377
                                                (fun uu____27481  ->
                                                   match uu____27481 with
                                                   | (l1,l2) ->
                                                       let uu____27554 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27554))
                                               in
                                            (match uu____27358 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27659 ->
                                       let uu____27660 =
                                         let uu____27666 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27666)
                                          in
                                       FStar_Errors.raise_error uu____27660 r
                                    in
                                 (match uu____27212 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27742 =
                                        let uu____27749 =
                                          let uu____27750 =
                                            let uu____27751 =
                                              let uu____27758 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27758,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27751
                                             in
                                          [uu____27750]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27749
                                          (fun b  ->
                                             let uu____27774 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27776 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27778 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27774 uu____27776
                                               uu____27778) r
                                         in
                                      (match uu____27742 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27788 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27788
                                             then
                                               let uu____27793 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27802 =
                                                          let uu____27804 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27804
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27802) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27793
                                             else ());
                                            (let wl4 =
                                               let uu___3597_27812 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3597_27812.attempting);
                                                 wl_deferred =
                                                   (uu___3597_27812.wl_deferred);
                                                 ctr = (uu___3597_27812.ctr);
                                                 defer_ok =
                                                   (uu___3597_27812.defer_ok);
                                                 smt_ok =
                                                   (uu___3597_27812.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3597_27812.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3597_27812.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27837 =
                                                        let uu____27844 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27844, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27837) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27861 =
                                               let f_sort_is =
                                                 let uu____27871 =
                                                   let uu____27872 =
                                                     let uu____27875 =
                                                       let uu____27876 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27876.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27875
                                                      in
                                                   uu____27872.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27871 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27887,uu____27888::is)
                                                     ->
                                                     let uu____27930 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____27930
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____27963 ->
                                                     let uu____27964 =
                                                       let uu____27970 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____27970)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____27964 r
                                                  in
                                               let uu____27976 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28011  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28011
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28032 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28032
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____27976
                                                in
                                             match uu____27861 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28057 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28057
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28058 =
                                                   let g_sort_is =
                                                     let uu____28068 =
                                                       let uu____28069 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28069.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28068 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28074,uu____28075::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28135 ->
                                                         let uu____28136 =
                                                           let uu____28142 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28142)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28136 r
                                                      in
                                                   let uu____28148 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28183  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28183
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28204
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28204
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28148
                                                    in
                                                 (match uu____28058 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28231 =
                                                          let uu____28236 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28237 =
                                                            let uu____28238 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28238
                                                             in
                                                          (uu____28236,
                                                            uu____28237)
                                                           in
                                                        match uu____28231
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28266 =
                                                          let uu____28269 =
                                                            let uu____28272 =
                                                              let uu____28275
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28275
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28272
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28269
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28266
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28299 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28299
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
                                                        let uu____28310 =
                                                          let uu____28313 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28316  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28316)
                                                            uu____28313
                                                           in
                                                        solve_prob orig
                                                          uu____28310 [] wl6
                                                         in
                                                      let uu____28317 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28317))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28340 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28342 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28342]
              | x -> x  in
            let c12 =
              let uu___3663_28345 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3663_28345.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3663_28345.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3663_28345.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3663_28345.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28346 =
              let uu____28351 =
                FStar_All.pipe_right
                  (let uu___3666_28353 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3666_28353.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3666_28353.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3666_28353.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3666_28353.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28351
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28346
              (fun uu____28367  ->
                 match uu____28367 with
                 | (c,g) ->
                     let uu____28374 =
                       let uu____28376 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28376  in
                     if uu____28374
                     then
                       let uu____28379 =
                         let uu____28385 =
                           let uu____28387 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28389 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28387 uu____28389
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28385)
                          in
                       FStar_Errors.raise_error uu____28379 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28395 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28395
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28401 = lift_c1 ()  in
               solve_eq uu____28401 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28410  ->
                         match uu___31_28410 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28415 -> false))
                  in
               let uu____28417 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28447)::uu____28448,(wp2,uu____28450)::uu____28451)
                     -> (wp1, wp2)
                 | uu____28524 ->
                     let uu____28549 =
                       let uu____28555 =
                         let uu____28557 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28559 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28557 uu____28559
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28555)
                        in
                     FStar_Errors.raise_error uu____28549
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28417 with
               | (wpc1,wpc2) ->
                   let uu____28569 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28569
                   then
                     let uu____28572 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28572 wl
                   else
                     (let uu____28576 =
                        let uu____28583 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28583  in
                      match uu____28576 with
                      | (c2_decl,qualifiers) ->
                          let uu____28604 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28604
                          then
                            let c1_repr =
                              let uu____28611 =
                                let uu____28612 =
                                  let uu____28613 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28613  in
                                let uu____28614 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28612 uu____28614
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28611
                               in
                            let c2_repr =
                              let uu____28617 =
                                let uu____28618 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28619 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28618 uu____28619
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28617
                               in
                            let uu____28621 =
                              let uu____28626 =
                                let uu____28628 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28630 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28628
                                  uu____28630
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28626
                               in
                            (match uu____28621 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28636 = attempt [prob] wl2  in
                                 solve env uu____28636)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28656 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28656
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28679 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28679
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
                                        let uu____28689 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28689 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28696 =
                                        let uu____28703 =
                                          let uu____28704 =
                                            let uu____28721 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28724 =
                                              let uu____28735 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28735; wpc1_2]  in
                                            (uu____28721, uu____28724)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28704
                                           in
                                        FStar_Syntax_Syntax.mk uu____28703
                                         in
                                      uu____28696
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
                                     let uu____28784 =
                                       let uu____28791 =
                                         let uu____28792 =
                                           let uu____28809 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28812 =
                                             let uu____28823 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28832 =
                                               let uu____28843 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28843; wpc1_2]  in
                                             uu____28823 :: uu____28832  in
                                           (uu____28809, uu____28812)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28792
                                          in
                                       FStar_Syntax_Syntax.mk uu____28791  in
                                     uu____28784 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28897 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28897
                              then
                                let uu____28902 =
                                  let uu____28904 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28904
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28902
                              else ());
                             (let uu____28908 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28908 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28917 =
                                      let uu____28920 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _28923  ->
                                           FStar_Pervasives_Native.Some
                                             _28923) uu____28920
                                       in
                                    solve_prob orig uu____28917 [] wl1  in
                                  let uu____28924 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28924))))
           in
        let uu____28925 = FStar_Util.physical_equality c1 c2  in
        if uu____28925
        then
          let uu____28928 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28928
        else
          ((let uu____28932 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28932
            then
              let uu____28937 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28939 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28937
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28939
            else ());
           (let uu____28944 =
              let uu____28953 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28956 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28953, uu____28956)  in
            match uu____28944 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28974),FStar_Syntax_Syntax.Total
                    (t2,uu____28976)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____28993 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28993 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28995,FStar_Syntax_Syntax.Total uu____28996) ->
                     let uu____29013 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29013 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29017),FStar_Syntax_Syntax.Total
                    (t2,uu____29019)) ->
                     let uu____29036 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29036 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29039),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29041)) ->
                     let uu____29058 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29058 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29061),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29063)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29080 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29080 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29083),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29085)) ->
                     let uu____29102 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29102 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29105,FStar_Syntax_Syntax.Comp uu____29106) ->
                     let uu____29115 =
                       let uu___3790_29118 = problem  in
                       let uu____29121 =
                         let uu____29122 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29122
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3790_29118.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29121;
                         FStar_TypeChecker_Common.relation =
                           (uu___3790_29118.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3790_29118.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3790_29118.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3790_29118.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3790_29118.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3790_29118.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3790_29118.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3790_29118.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29115 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29123,FStar_Syntax_Syntax.Comp uu____29124) ->
                     let uu____29133 =
                       let uu___3790_29136 = problem  in
                       let uu____29139 =
                         let uu____29140 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29140
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3790_29136.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29139;
                         FStar_TypeChecker_Common.relation =
                           (uu___3790_29136.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3790_29136.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3790_29136.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3790_29136.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3790_29136.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3790_29136.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3790_29136.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3790_29136.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29133 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29141,FStar_Syntax_Syntax.GTotal uu____29142) ->
                     let uu____29151 =
                       let uu___3802_29154 = problem  in
                       let uu____29157 =
                         let uu____29158 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29158
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3802_29154.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3802_29154.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3802_29154.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29157;
                         FStar_TypeChecker_Common.element =
                           (uu___3802_29154.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3802_29154.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3802_29154.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3802_29154.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3802_29154.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3802_29154.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29151 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29159,FStar_Syntax_Syntax.Total uu____29160) ->
                     let uu____29169 =
                       let uu___3802_29172 = problem  in
                       let uu____29175 =
                         let uu____29176 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29176
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3802_29172.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3802_29172.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3802_29172.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29175;
                         FStar_TypeChecker_Common.element =
                           (uu___3802_29172.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3802_29172.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3802_29172.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3802_29172.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3802_29172.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3802_29172.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29169 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29177,FStar_Syntax_Syntax.Comp uu____29178) ->
                     let uu____29179 =
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
                     if uu____29179
                     then
                       let uu____29182 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29182 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29189 =
                            let uu____29194 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29194
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29203 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29204 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29203, uu____29204))
                             in
                          match uu____29189 with
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
                           (let uu____29212 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29212
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29220 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29220 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29223 =
                                  FStar_Thunk.mk
                                    (fun uu____29228  ->
                                       let uu____29229 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29231 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29229 uu____29231)
                                   in
                                giveup env uu____29223 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29242 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29242 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29292 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29292 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29317 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29348  ->
                match uu____29348 with
                | (u1,u2) ->
                    let uu____29356 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29358 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29356 uu____29358))
         in
      FStar_All.pipe_right uu____29317 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29395,[])) when
          let uu____29422 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29422 -> "{}"
      | uu____29425 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29452 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29452
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29464 =
              FStar_List.map
                (fun uu____29477  ->
                   match uu____29477 with
                   | (uu____29484,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29464 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29495 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29495 imps
  
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
                  let uu____29552 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29552
                  then
                    let uu____29560 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29562 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29560
                      (rel_to_string rel) uu____29562
                  else "TOP"  in
                let uu____29568 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29568 with
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
              let uu____29628 =
                let uu____29631 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29634  -> FStar_Pervasives_Native.Some _29634)
                  uu____29631
                 in
              FStar_Syntax_Syntax.new_bv uu____29628 t1  in
            let uu____29635 =
              let uu____29640 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29640
               in
            match uu____29635 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29698 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29698
         then
           let uu____29703 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29703
         else ());
        (let uu____29710 =
           FStar_Util.record_time (fun uu____29717  -> solve env probs)  in
         match uu____29710 with
         | (sol,ms) ->
             ((let uu____29729 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29729
               then
                 let uu____29734 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29734
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29747 =
                     FStar_Util.record_time
                       (fun uu____29754  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29747 with
                    | ((),ms1) ->
                        ((let uu____29765 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29765
                          then
                            let uu____29770 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29770
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29782 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29782
                     then
                       let uu____29789 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29789
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
          ((let uu____29815 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29815
            then
              let uu____29820 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29820
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29828 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29828
             then
               let uu____29833 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29833
             else ());
            (let f2 =
               let uu____29839 =
                 let uu____29840 = FStar_Syntax_Util.unmeta f1  in
                 uu____29840.FStar_Syntax_Syntax.n  in
               match uu____29839 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29844 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3919_29845 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3919_29845.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3919_29845.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3919_29845.FStar_TypeChecker_Common.implicits)
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
            let uu____29888 =
              let uu____29889 =
                let uu____29890 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29891  ->
                       FStar_TypeChecker_Common.NonTrivial _29891)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29890;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29889  in
            FStar_All.pipe_left
              (fun _29898  -> FStar_Pervasives_Native.Some _29898)
              uu____29888
  
let with_guard_no_simp :
  'Auu____29908 .
    'Auu____29908 ->
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
            let uu____29948 =
              let uu____29949 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29950  -> FStar_TypeChecker_Common.NonTrivial _29950)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29949;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____29948
  
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
          (let uu____29983 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____29983
           then
             let uu____29988 = FStar_Syntax_Print.term_to_string t1  in
             let uu____29990 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____29988
               uu____29990
           else ());
          (let uu____29995 =
             let uu____30000 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30000
              in
           match uu____29995 with
           | (prob,wl) ->
               let g =
                 let uu____30008 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30016  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30008  in
               ((let uu____30034 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30034
                 then
                   let uu____30039 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30039
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
        let uu____30060 = try_teq true env t1 t2  in
        match uu____30060 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30065 = FStar_TypeChecker_Env.get_range env  in
              let uu____30066 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30065 uu____30066);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30074 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30074
              then
                let uu____30079 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30081 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30083 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30079
                  uu____30081 uu____30083
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
        (let uu____30107 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30107
         then
           let uu____30112 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30114 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30112
             uu____30114
         else ());
        (let uu____30119 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30119 with
         | (prob,x,wl) ->
             let g =
               let uu____30134 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30143  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30134  in
             ((let uu____30161 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30161
               then
                 let uu____30166 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30166
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30174 =
                     let uu____30175 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30175 g1  in
                   FStar_Pervasives_Native.Some uu____30174)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30197 = FStar_TypeChecker_Env.get_range env  in
          let uu____30198 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30197 uu____30198
  
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
        (let uu____30227 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30227
         then
           let uu____30232 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30234 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30232 uu____30234
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30245 =
           let uu____30252 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30252 "sub_comp"
            in
         match uu____30245 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30265 =
                 FStar_Util.record_time
                   (fun uu____30277  ->
                      let uu____30278 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30287  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30278)
                  in
               match uu____30265 with
               | (r,ms) ->
                   ((let uu____30315 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30315
                     then
                       let uu____30320 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30322 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30324 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30320 uu____30322
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30324
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
      fun uu____30362  ->
        match uu____30362 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30405 =
                 let uu____30411 =
                   let uu____30413 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30415 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30413 uu____30415
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30411)  in
               let uu____30419 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30405 uu____30419)
               in
            let equiv1 v1 v' =
              let uu____30432 =
                let uu____30437 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30438 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30437, uu____30438)  in
              match uu____30432 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30458 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____30489 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30489 with
                      | FStar_Syntax_Syntax.U_unif uu____30496 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30525  ->
                                    match uu____30525 with
                                    | (u,v') ->
                                        let uu____30534 = equiv1 v1 v'  in
                                        if uu____30534
                                        then
                                          let uu____30539 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30539 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____30560 -> []))
               in
            let uu____30565 =
              let wl =
                let uu___4030_30569 = empty_worklist env  in
                {
                  attempting = (uu___4030_30569.attempting);
                  wl_deferred = (uu___4030_30569.wl_deferred);
                  ctr = (uu___4030_30569.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4030_30569.smt_ok);
                  umax_heuristic_ok = (uu___4030_30569.umax_heuristic_ok);
                  tcenv = (uu___4030_30569.tcenv);
                  wl_implicits = (uu___4030_30569.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30588  ->
                      match uu____30588 with
                      | (lb,v1) ->
                          let uu____30595 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30595 with
                           | USolved wl1 -> ()
                           | uu____30598 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30609 =
              match uu____30609 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30621) -> true
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
                      uu____30645,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30647,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30658) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30666,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30675 -> false)
               in
            let uu____30681 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30698  ->
                      match uu____30698 with
                      | (u,v1) ->
                          let uu____30706 = check_ineq (u, v1)  in
                          if uu____30706
                          then true
                          else
                            ((let uu____30714 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30714
                              then
                                let uu____30719 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30721 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30719
                                  uu____30721
                              else ());
                             false)))
               in
            if uu____30681
            then ()
            else
              ((let uu____30731 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30731
                then
                  ((let uu____30737 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30737);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30749 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30749))
                else ());
               (let uu____30762 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30762))
  
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
        let fail1 uu____30835 =
          match uu____30835 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4107_30858 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4107_30858.attempting);
            wl_deferred = (uu___4107_30858.wl_deferred);
            ctr = (uu___4107_30858.ctr);
            defer_ok;
            smt_ok = (uu___4107_30858.smt_ok);
            umax_heuristic_ok = (uu___4107_30858.umax_heuristic_ok);
            tcenv = (uu___4107_30858.tcenv);
            wl_implicits = (uu___4107_30858.wl_implicits)
          }  in
        (let uu____30861 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30861
         then
           let uu____30866 = FStar_Util.string_of_bool defer_ok  in
           let uu____30868 = wl_to_string wl  in
           let uu____30870 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30866 uu____30868 uu____30870
         else ());
        (let g1 =
           let uu____30876 = solve_and_commit env wl fail1  in
           match uu____30876 with
           | FStar_Pervasives_Native.Some
               (uu____30883::uu____30884,uu____30885) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4122_30914 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4122_30914.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4122_30914.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30915 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4127_30924 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4127_30924.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4127_30924.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4127_30924.FStar_TypeChecker_Common.implicits)
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
            let uu___4139_31001 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4139_31001.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4139_31001.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4139_31001.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____31002 =
            let uu____31004 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____31004  in
          if uu____31002
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____31016 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____31017 =
                       let uu____31019 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____31019
                        in
                     FStar_Errors.diag uu____31016 uu____31017)
                  else ();
                  (let vc1 =
                     let uu____31025 =
                       let uu____31029 =
                         let uu____31031 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____31031  in
                       FStar_Pervasives_Native.Some uu____31029  in
                     FStar_Profiling.profile
                       (fun uu____31034  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____31025 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug1
                   then
                     (let uu____31038 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31039 =
                        let uu____31041 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31041
                         in
                      FStar_Errors.diag uu____31038 uu____31039)
                   else ();
                   (let uu____31047 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31047
                      "discharge_guard'" env vc1);
                   (let uu____31049 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31049 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____31058 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31059 =
                                let uu____31061 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31061
                                 in
                              FStar_Errors.diag uu____31058 uu____31059)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____31071 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31072 =
                                let uu____31074 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31074
                                 in
                              FStar_Errors.diag uu____31071 uu____31072)
                           else ();
                           (let vcs =
                              let uu____31088 = FStar_Options.use_tactics ()
                                 in
                              if uu____31088
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31110  ->
                                     (let uu____31112 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____31112);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31156  ->
                                              match uu____31156 with
                                              | (env1,goal,opts) ->
                                                  let uu____31172 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31172, opts)))))
                              else
                                (let uu____31176 =
                                   let uu____31183 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31183)  in
                                 [uu____31176])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31216  ->
                                    match uu____31216 with
                                    | (env1,goal,opts) ->
                                        let uu____31226 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31226 with
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
                                                (let uu____31237 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31238 =
                                                   let uu____31240 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31242 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31240 uu____31242
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31237 uu____31238)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____31249 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31250 =
                                                   let uu____31252 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31252
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31249 uu____31250)
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
      let uu____31270 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31270 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31279 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31279
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31293 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31293 with
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
        let uu____31323 = try_teq false env t1 t2  in
        match uu____31323 with
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
            let uu____31367 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31367 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31380 ->
                     let uu____31393 =
                       let uu____31394 = FStar_Syntax_Subst.compress r  in
                       uu____31394.FStar_Syntax_Syntax.n  in
                     (match uu____31393 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31399) ->
                          unresolved ctx_u'
                      | uu____31416 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31440 = acc  in
            match uu____31440 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____31459 = hd1  in
                     (match uu____31459 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____31470 = unresolved ctx_u  in
                             if uu____31470
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31494 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31494
                                     then
                                       let uu____31498 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31498
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31507 = teq_nosmt env1 t tm
                                          in
                                       match uu____31507 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4252_31517 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4252_31517.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4252_31517.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4252_31517.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4252_31517.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4252_31517.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4252_31517.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4252_31517.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4255_31525 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4255_31525.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4255_31525.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4255_31525.FStar_TypeChecker_Common.imp_range)
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
                                    let uu___4259_31536 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4259_31536.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4259_31536.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4259_31536.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4259_31536.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4259_31536.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4259_31536.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4259_31536.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4259_31536.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4259_31536.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4259_31536.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4259_31536.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4259_31536.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4259_31536.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4259_31536.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4259_31536.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4259_31536.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4259_31536.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4259_31536.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4259_31536.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4259_31536.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4259_31536.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4259_31536.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4259_31536.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4259_31536.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4259_31536.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4259_31536.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4259_31536.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4259_31536.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4259_31536.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4259_31536.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4259_31536.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4259_31536.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4259_31536.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4259_31536.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4259_31536.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4259_31536.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4259_31536.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4259_31536.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4259_31536.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4259_31536.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4259_31536.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4259_31536.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4259_31536.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4259_31536.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4259_31536.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4259_31536.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4264_31541 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4264_31541.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4264_31541.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4264_31541.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4264_31541.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4264_31541.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4264_31541.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4264_31541.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4264_31541.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4264_31541.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4264_31541.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4264_31541.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4264_31541.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4264_31541.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4264_31541.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4264_31541.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4264_31541.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4264_31541.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4264_31541.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4264_31541.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4264_31541.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4264_31541.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4264_31541.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4264_31541.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4264_31541.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4264_31541.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4264_31541.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4264_31541.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4264_31541.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4264_31541.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4264_31541.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4264_31541.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4264_31541.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4264_31541.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4264_31541.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4264_31541.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4264_31541.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4264_31541.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4264_31541.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4264_31541.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4264_31541.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4264_31541.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4264_31541.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4264_31541.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4264_31541.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4264_31541.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4264_31541.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31546 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31546
                                   then
                                     let uu____31551 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31553 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31555 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31557 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31551 uu____31553 uu____31555
                                       reason uu____31557
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4270_31564  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31571 =
                                             let uu____31581 =
                                               let uu____31589 =
                                                 let uu____31591 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31593 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31595 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31591 uu____31593
                                                   uu____31595
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31589, r)
                                                in
                                             [uu____31581]  in
                                           FStar_Errors.add_errors
                                             uu____31571);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31614 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31625  ->
                                               let uu____31626 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31628 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31630 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31626 uu____31628
                                                 reason uu____31630)) env2 g1
                                         true
                                        in
                                     match uu____31614 with
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
          let uu___4282_31638 = g  in
          let uu____31639 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4282_31638.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4282_31638.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4282_31638.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31639
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
        let uu____31679 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31679 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31680 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31680
      | imp::uu____31682 ->
          let uu____31685 =
            let uu____31691 =
              let uu____31693 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31695 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31693 uu____31695
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31691)
             in
          FStar_Errors.raise_error uu____31685
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31715 = teq env t1 t2  in
        force_trivial_guard env uu____31715
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31734 = teq_nosmt env t1 t2  in
        match uu____31734 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4307_31753 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4307_31753.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4307_31753.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4307_31753.FStar_TypeChecker_Common.implicits)
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
        (let uu____31789 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31789
         then
           let uu____31794 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31796 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31794
             uu____31796
         else ());
        (let uu____31801 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31801 with
         | (prob,x,wl) ->
             let g =
               let uu____31820 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31829  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31820  in
             ((let uu____31847 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31847
               then
                 let uu____31852 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31854 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31856 =
                   let uu____31858 = FStar_Util.must g  in
                   guard_to_string env uu____31858  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31852 uu____31854 uu____31856
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
        let uu____31895 = check_subtyping env t1 t2  in
        match uu____31895 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31914 =
              let uu____31915 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31915 g  in
            FStar_Pervasives_Native.Some uu____31914
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31934 = check_subtyping env t1 t2  in
        match uu____31934 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31953 =
              let uu____31954 =
                let uu____31955 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31955]  in
              FStar_TypeChecker_Env.close_guard env uu____31954 g  in
            FStar_Pervasives_Native.Some uu____31953
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____31993 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31993
         then
           let uu____31998 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32000 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____31998
             uu____32000
         else ());
        (let uu____32005 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32005 with
         | (prob,x,wl) ->
             let g =
               let uu____32020 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32029  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32020  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32050 =
                      let uu____32051 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32051]  in
                    FStar_TypeChecker_Env.close_guard env uu____32050 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32092 = subtype_nosmt env t1 t2  in
        match uu____32092 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  