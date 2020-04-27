open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type lstring = Prims.string FStar_Thunk.t
let (mklstr : (unit -> Prims.string) -> Prims.string FStar_Thunk.thunk) =
  fun f  ->
    let uf = FStar_Syntax_Unionfind.get ()  in
    FStar_Thunk.mk
      (fun uu____41  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         FStar_Syntax_Unionfind.set uf;
         (let r = f ()  in FStar_Syntax_Unionfind.rollback tx; r))
  
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____79 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____114 -> false
  
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
  wl_implicits: FStar_TypeChecker_Common.implicits ;
  repr_subcomp_allowed: Prims.bool }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits; repr_subcomp_allowed;_} -> attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits; repr_subcomp_allowed;_} -> wl_deferred
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits; repr_subcomp_allowed;_} -> ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits; repr_subcomp_allowed;_} -> defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits; repr_subcomp_allowed;_} -> smt_ok
  
let (__proj__Mkworklist__item__umax_heuristic_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits; repr_subcomp_allowed;_} -> umax_heuristic_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits; repr_subcomp_allowed;_} -> tcenv
  
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Common.implicits) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits; repr_subcomp_allowed;_} -> wl_implicits
  
let (__proj__Mkworklist__item__repr_subcomp_allowed : worklist -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits; repr_subcomp_allowed;_} -> repr_subcomp_allowed
  
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
                    let uu____624 = FStar_Syntax_Unionfind.fresh r  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____624;
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
                   (let uu____658 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace")
                       in
                    if uu____658
                    then
                      let uu____662 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                         in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____662
                    else ());
                   (ctx_uvar, t,
                     ((let uu___80_668 = wl  in
                       {
                         attempting = (uu___80_668.attempting);
                         wl_deferred = (uu___80_668.wl_deferred);
                         ctr = (uu___80_668.ctr);
                         defer_ok = (uu___80_668.defer_ok);
                         smt_ok = (uu___80_668.smt_ok);
                         umax_heuristic_ok = (uu___80_668.umax_heuristic_ok);
                         tcenv = (uu___80_668.tcenv);
                         wl_implicits = (imp :: (wl.wl_implicits));
                         repr_subcomp_allowed =
                           (uu___80_668.repr_subcomp_allowed)
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
            let uu___86_701 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___86_701.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___86_701.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___86_701.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___86_701.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___86_701.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___86_701.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___86_701.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___86_701.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___86_701.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___86_701.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___86_701.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___86_701.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___86_701.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___86_701.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___86_701.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___86_701.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___86_701.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___86_701.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___86_701.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___86_701.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___86_701.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___86_701.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___86_701.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___86_701.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___86_701.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___86_701.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___86_701.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___86_701.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___86_701.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___86_701.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___86_701.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___86_701.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___86_701.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___86_701.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___86_701.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___86_701.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___86_701.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___86_701.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___86_701.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___86_701.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___86_701.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___86_701.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___86_701.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___86_701.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___86_701.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____703 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____703 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____790 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____825 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____855 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____866 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____877 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_895  ->
    match uu___0_895 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____907 = FStar_Syntax_Util.head_and_args t  in
    match uu____907 with
    | (head,args) ->
        (match head.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____970 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____972 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____987 =
                     let uu____989 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____989  in
                   FStar_Util.format1 "@<%s>" uu____987
                in
             let uu____993 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____970 uu____972 uu____993
         | uu____996 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_1008  ->
      match uu___1_1008 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1013 =
            let uu____1017 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1019 =
              let uu____1023 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1025 =
                let uu____1029 =
                  let uu____1033 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1033]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1029
                 in
              uu____1023 :: uu____1025  in
            uu____1017 :: uu____1019  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____1013
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1044 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1046 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1048 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1044 uu____1046
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1048
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_1062  ->
      match uu___2_1062 with
      | UNIV (u,t) ->
          let x =
            let uu____1068 = FStar_Options.hide_uvar_nums ()  in
            if uu____1068
            then "?"
            else
              (let uu____1075 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1075 FStar_Util.string_of_int)
             in
          let uu____1079 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s <- %s" x uu____1079
      | TERM (u,t) ->
          let x =
            let uu____1086 = FStar_Options.hide_uvar_nums ()  in
            if uu____1086
            then "?"
            else
              (let uu____1093 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1093 FStar_Util.string_of_int)
             in
          let uu____1097 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s <- %s" x uu____1097
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  -> FStar_Common.string_of_list (uvi_to_string env) uvis
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1127 =
      let uu____1131 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1131
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1127 (FStar_String.concat ", ")
  
let args_to_string :
  'uuuuuu1150 .
    (FStar_Syntax_Syntax.term * 'uuuuuu1150) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1169 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1190  ->
              match uu____1190 with
              | (x,uu____1197) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1169 (FStar_String.concat " ")
  
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
      wl_implicits = [];
      repr_subcomp_allowed = false
    }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    lstring -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1238 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1238
         then
           let uu____1243 = FStar_Thunk.force reason  in
           let uu____1246 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1243 uu____1246
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1269 = mklstr (fun uu____1272  -> reason)  in
        giveup env uu____1269 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1278  ->
    match uu___3_1278 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'uuuuuu1284 .
    'uuuuuu1284 FStar_TypeChecker_Common.problem ->
      'uuuuuu1284 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___150_1296 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___150_1296.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___150_1296.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___150_1296.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___150_1296.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___150_1296.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___150_1296.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___150_1296.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'uuuuuu1304 .
    'uuuuuu1304 FStar_TypeChecker_Common.problem ->
      'uuuuuu1304 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1324  ->
    match uu___4_1324 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1330  -> FStar_TypeChecker_Common.TProb uu____1330)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1336  -> FStar_TypeChecker_Common.CProb uu____1336)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1342  ->
    match uu___5_1342 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___162_1348 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___162_1348.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___162_1348.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___162_1348.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___162_1348.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___162_1348.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___162_1348.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___162_1348.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___162_1348.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___162_1348.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___166_1356 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___166_1356.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___166_1356.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___166_1356.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___166_1356.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___166_1356.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___166_1356.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___166_1356.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___166_1356.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___166_1356.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1369  ->
      match uu___6_1369 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1376  ->
    match uu___7_1376 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1389  ->
    match uu___8_1389 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1404  ->
    match uu___9_1404 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1419  ->
    match uu___10_1419 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1433  ->
    match uu___11_1433 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1447  ->
    match uu___12_1447 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1459  ->
    match uu___13_1459 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'uuuuuu1475 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu1475) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1505 =
          let uu____1507 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1507  in
        if uu____1505
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1544)::bs ->
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
          let uu____1591 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1615 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1615]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1591
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1643 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1667 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1667]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1643
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1714 =
          let uu____1716 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1716  in
        if uu____1714
        then ()
        else
          (let uu____1721 =
             let uu____1724 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1724
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1721 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1773 =
          let uu____1775 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1775  in
        if uu____1773
        then ()
        else
          (let uu____1780 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1780)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1800 =
        let uu____1802 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1802  in
      if uu____1800
      then ()
      else
        (let msgf m =
           let uu____1816 =
             let uu____1818 =
               let uu____1820 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____1820 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____1818  in
           Prims.op_Hat msg uu____1816  in
         (let uu____1825 = msgf "scope"  in
          let uu____1828 = p_scope prob  in
          def_scope_wf uu____1825 (p_loc prob) uu____1828);
         (let uu____1840 = msgf "guard"  in
          def_check_scoped uu____1840 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1847 = msgf "lhs"  in
                def_check_scoped uu____1847 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1850 = msgf "rhs"  in
                def_check_scoped uu____1850 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1857 = msgf "lhs"  in
                def_check_scoped_comp uu____1857 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1860 = msgf "rhs"  in
                def_check_scoped_comp uu____1860 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___259_1881 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___259_1881.wl_deferred);
          ctr = (uu___259_1881.ctr);
          defer_ok = (uu___259_1881.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___259_1881.umax_heuristic_ok);
          tcenv = (uu___259_1881.tcenv);
          wl_implicits = (uu___259_1881.wl_implicits);
          repr_subcomp_allowed = (uu___259_1881.repr_subcomp_allowed)
        }
  
let wl_of_guard :
  'uuuuuu1889 .
    FStar_TypeChecker_Env.env ->
      ('uuuuuu1889 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___263_1912 = empty_worklist env  in
      let uu____1913 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1913;
        wl_deferred = (uu___263_1912.wl_deferred);
        ctr = (uu___263_1912.ctr);
        defer_ok = (uu___263_1912.defer_ok);
        smt_ok = (uu___263_1912.smt_ok);
        umax_heuristic_ok = (uu___263_1912.umax_heuristic_ok);
        tcenv = (uu___263_1912.tcenv);
        wl_implicits = (uu___263_1912.wl_implicits);
        repr_subcomp_allowed = (uu___263_1912.repr_subcomp_allowed)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___268_1934 = wl  in
        {
          attempting = (uu___268_1934.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___268_1934.ctr);
          defer_ok = (uu___268_1934.defer_ok);
          smt_ok = (uu___268_1934.smt_ok);
          umax_heuristic_ok = (uu___268_1934.umax_heuristic_ok);
          tcenv = (uu___268_1934.tcenv);
          wl_implicits = (uu___268_1934.wl_implicits);
          repr_subcomp_allowed = (uu___268_1934.repr_subcomp_allowed)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____1961 = FStar_Thunk.mkv reason  in defer uu____1961 prob wl
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___276_1980 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___276_1980.wl_deferred);
         ctr = (uu___276_1980.ctr);
         defer_ok = (uu___276_1980.defer_ok);
         smt_ok = (uu___276_1980.smt_ok);
         umax_heuristic_ok = (uu___276_1980.umax_heuristic_ok);
         tcenv = (uu___276_1980.tcenv);
         wl_implicits = (uu___276_1980.wl_implicits);
         repr_subcomp_allowed = (uu___276_1980.repr_subcomp_allowed)
       })
  
let mk_eq2 :
  'uuuuuu1994 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu1994 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____2028 = FStar_Syntax_Util.type_u ()  in
            match uu____2028 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____2040 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____2040 with
                 | (uu____2058,tt,wl1) ->
                     let uu____2061 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____2061, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2067  ->
    match uu___14_2067 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun uu____2073  -> FStar_TypeChecker_Common.TProb uu____2073)
          (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun uu____2079  -> FStar_TypeChecker_Common.CProb uu____2079)
          (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2087 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2087 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2107  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'uuuuuu2149 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'uuuuuu2149 ->
            FStar_TypeChecker_Common.rel ->
              'uuuuuu2149 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('uuuuuu2149 FStar_TypeChecker_Common.problem * worklist)
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
                        let uu____2236 =
                          let uu____2245 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2245]  in
                        FStar_List.append scope uu____2236
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2288 =
                      let uu____2291 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2291  in
                    FStar_List.append uu____2288
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2310 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2310 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2336 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2336;
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
                  (let uu____2410 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2410 with
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
                  (let uu____2498 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2498 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'uuuuuu2536 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu2536 ->
          FStar_TypeChecker_Common.rel ->
            'uuuuuu2536 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('uuuuuu2536 FStar_TypeChecker_Common.problem * worklist)
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
                          let uu____2604 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2604]  in
                        let uu____2623 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2623
                     in
                  let uu____2626 =
                    let uu____2633 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___359_2644 = wl  in
                       {
                         attempting = (uu___359_2644.attempting);
                         wl_deferred = (uu___359_2644.wl_deferred);
                         ctr = (uu___359_2644.ctr);
                         defer_ok = (uu___359_2644.defer_ok);
                         smt_ok = (uu___359_2644.smt_ok);
                         umax_heuristic_ok =
                           (uu___359_2644.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___359_2644.wl_implicits);
                         repr_subcomp_allowed =
                           (uu___359_2644.repr_subcomp_allowed)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2633
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2626 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2662 =
                              let uu____2667 =
                                let uu____2668 =
                                  let uu____2677 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2677
                                   in
                                [uu____2668]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2667  in
                            uu____2662 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2705 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2705;
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
                let uu____2753 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2753;
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
  'uuuuuu2768 .
    worklist ->
      'uuuuuu2768 FStar_TypeChecker_Common.problem ->
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
              let uu____2801 =
                let uu____2804 =
                  let uu____2805 =
                    let uu____2812 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2812)  in
                  FStar_Syntax_Syntax.NT uu____2805  in
                [uu____2804]  in
              FStar_Syntax_Subst.subst uu____2801 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2834 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2834
        then
          let uu____2842 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2845 = prob_to_string env d  in
          let uu____2847 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____2854 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2842 uu____2845 uu____2847 uu____2854
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2866 -> failwith "impossible"  in
           let uu____2869 =
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
           match uu____2869 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2912  ->
            match uu___15_2912 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2926 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2930 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2930 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2961  ->
           match uu___16_2961 with
           | UNIV uu____2964 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2971 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2971
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
        (fun uu___17_2999  ->
           match uu___17_2999 with
           | UNIV (u',t) ->
               let uu____3004 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____3004
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____3011 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3023 =
        let uu____3024 =
          let uu____3025 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____3025
           in
        FStar_Syntax_Subst.compress uu____3024  in
      FStar_All.pipe_right uu____3023 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3037 =
        let uu____3038 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____3038  in
      FStar_All.pipe_right uu____3037 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3050 =
        let uu____3054 =
          let uu____3056 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3056  in
        FStar_Pervasives_Native.Some uu____3054  in
      FStar_Profiling.profile (fun uu____3059  -> sn' env t) uu____3050
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
          let uu____3084 =
            let uu____3088 =
              let uu____3090 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3090  in
            FStar_Pervasives_Native.Some uu____3088  in
          FStar_Profiling.profile
            (fun uu____3093  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3084
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3101 = FStar_Syntax_Util.head_and_args t  in
    match uu____3101 with
    | (h,uu____3120) ->
        let uu____3145 =
          let uu____3146 = FStar_Syntax_Subst.compress h  in
          uu____3146.FStar_Syntax_Syntax.n  in
        (match uu____3145 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3151 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3164 =
        let uu____3168 =
          let uu____3170 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3170  in
        FStar_Pervasives_Native.Some uu____3168  in
      FStar_Profiling.profile
        (fun uu____3175  ->
           let uu____3176 = should_strongly_reduce t  in
           if uu____3176
           then
             let uu____3179 =
               let uu____3180 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3180  in
             FStar_All.pipe_right uu____3179 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3164 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'uuuuuu3191 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'uuuuuu3191) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu3191)
  =
  fun env  ->
    fun t  ->
      let uu____3214 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3214, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3266  ->
              match uu____3266 with
              | (x,imp) ->
                  let uu____3285 =
                    let uu___465_3286 = x  in
                    let uu____3287 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___465_3286.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___465_3286.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3287
                    }  in
                  (uu____3285, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3311 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3311
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3315 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3315
        | uu____3318 -> u2  in
      let uu____3319 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3319
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3336 =
          let uu____3340 =
            let uu____3342 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3342  in
          FStar_Pervasives_Native.Some uu____3340  in
        FStar_Profiling.profile
          (fun uu____3345  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3336 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
        let rec aux norm t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____3467 = norm_refinement env t12  in
                 match uu____3467 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3482;
                     FStar_Syntax_Syntax.vars = uu____3483;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3507 =
                       let uu____3509 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3511 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3509 uu____3511
                        in
                     failwith uu____3507)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3527 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm uu____3527
          | FStar_Syntax_Syntax.Tm_uinst uu____3528 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3565 =
                   let uu____3566 = FStar_Syntax_Subst.compress t1'  in
                   uu____3566.FStar_Syntax_Syntax.n  in
                 match uu____3565 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3581 -> aux true t1'
                 | uu____3589 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3604 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3635 =
                   let uu____3636 = FStar_Syntax_Subst.compress t1'  in
                   uu____3636.FStar_Syntax_Syntax.n  in
                 match uu____3635 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3651 -> aux true t1'
                 | uu____3659 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3674 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3721 =
                   let uu____3722 = FStar_Syntax_Subst.compress t1'  in
                   uu____3722.FStar_Syntax_Syntax.n  in
                 match uu____3721 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3737 -> aux true t1'
                 | uu____3745 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3760 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3775 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3790 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3805 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3820 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3849 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3882 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3903 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3930 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3958 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3995 ->
              let uu____4002 =
                let uu____4004 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4006 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4004 uu____4006
                 in
              failwith uu____4002
          | FStar_Syntax_Syntax.Tm_ascribed uu____4021 ->
              let uu____4048 =
                let uu____4050 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4052 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4050 uu____4052
                 in
              failwith uu____4048
          | FStar_Syntax_Syntax.Tm_delayed uu____4067 ->
              let uu____4082 =
                let uu____4084 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4086 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4084 uu____4086
                 in
              failwith uu____4082
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4101 =
                let uu____4103 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4105 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4103 uu____4105
                 in
              failwith uu____4101
           in
        let uu____4120 = whnf env t1  in aux false uu____4120
  
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
      let uu____4165 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4165 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4206 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4206, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta  ->
    fun env  ->
      fun t  ->
        let uu____4233 = base_and_refinement_maybe_delta delta env t  in
        match uu____4233 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4293  ->
    match uu____4293 with
    | (t_base,refopt) ->
        let uu____4324 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4324 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4366 =
      let uu____4370 =
        let uu____4373 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4398  ->
                  match uu____4398 with | (uu____4406,uu____4407,x) -> x))
           in
        FStar_List.append wl.attempting uu____4373  in
      FStar_List.map (wl_prob_to_string wl) uu____4370  in
    FStar_All.pipe_right uu____4366 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'uuuuuu4428 .
    ('uuuuuu4428 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4440  ->
    match uu____4440 with
    | (uu____4447,c,args) ->
        let uu____4450 = print_ctx_uvar c  in
        let uu____4452 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4450 uu____4452
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4462 = FStar_Syntax_Util.head_and_args t  in
    match uu____4462 with
    | (head,_args) ->
        let uu____4506 =
          let uu____4507 = FStar_Syntax_Subst.compress head  in
          uu____4507.FStar_Syntax_Syntax.n  in
        (match uu____4506 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4511 -> true
         | uu____4525 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4533 = FStar_Syntax_Util.head_and_args t  in
    match uu____4533 with
    | (head,_args) ->
        let uu____4576 =
          let uu____4577 = FStar_Syntax_Subst.compress head  in
          uu____4577.FStar_Syntax_Syntax.n  in
        (match uu____4576 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4581) -> u
         | uu____4598 -> failwith "Not a flex-uvar")
  
let (ensure_no_uvar_subst :
  FStar_Syntax_Syntax.term ->
    worklist -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun t0  ->
    fun wl  ->
      let bv_not_affected_by s x =
        let t_x = FStar_Syntax_Syntax.bv_to_name x  in
        let t_x' = FStar_Syntax_Subst.subst' s t_x  in
        let uu____4634 =
          let uu____4635 = FStar_Syntax_Subst.compress t_x'  in
          uu____4635.FStar_Syntax_Syntax.n  in
        match uu____4634 with
        | FStar_Syntax_Syntax.Tm_name y -> FStar_Syntax_Syntax.bv_eq x y
        | uu____4640 -> false  in
      let binding_not_affected_by s b =
        match b with
        | FStar_Syntax_Syntax.Binding_var x -> bv_not_affected_by s x
        | uu____4656 -> true  in
      let uu____4658 = FStar_Syntax_Util.head_and_args t0  in
      match uu____4658 with
      | (head,args) ->
          let uu____4705 =
            let uu____4706 = FStar_Syntax_Subst.compress head  in
            uu____4706.FStar_Syntax_Syntax.n  in
          (match uu____4705 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4714)) -> (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,uu____4730) when
               FStar_List.isEmpty uv.FStar_Syntax_Syntax.ctx_uvar_binders ->
               (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4771 =
                 FStar_Common.max_suffix (binding_not_affected_by s)
                   uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               (match uu____4771 with
                | (gamma_aff,new_gamma) ->
                    (match gamma_aff with
                     | [] -> (t0, wl)
                     | uu____4798 ->
                         let dom_binders =
                           FStar_TypeChecker_Env.binders_of_bindings
                             gamma_aff
                            in
                         let uu____4802 =
                           let uu____4809 =
                             FStar_TypeChecker_Env.binders_of_bindings
                               new_gamma
                              in
                           let uu____4818 =
                             let uu____4821 =
                               FStar_Syntax_Syntax.mk_Total
                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             FStar_Syntax_Util.arrow dom_binders uu____4821
                              in
                           new_uvar
                             (Prims.op_Hat
                                uv.FStar_Syntax_Syntax.ctx_uvar_reason
                                "; force delayed") wl
                             t0.FStar_Syntax_Syntax.pos new_gamma uu____4809
                             uu____4818
                             uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                             uv.FStar_Syntax_Syntax.ctx_uvar_meta
                            in
                         (match uu____4802 with
                          | (v,t_v,wl1) ->
                              let args_sol =
                                FStar_List.map
                                  (fun uu____4857  ->
                                     match uu____4857 with
                                     | (x,i) ->
                                         let uu____4876 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____4876, i)) dom_binders
                                 in
                              let sol =
                                FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                                  FStar_Pervasives_Native.None
                                  t0.FStar_Syntax_Syntax.pos
                                 in
                              (FStar_Syntax_Util.set_uvar
                                 uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                               (let args_sol_s =
                                  FStar_List.map
                                    (fun uu____4908  ->
                                       match uu____4908 with
                                       | (a,i) ->
                                           let uu____4927 =
                                             FStar_Syntax_Subst.subst' s a
                                              in
                                           (uu____4927, i)) args_sol
                                   in
                                let t =
                                  FStar_Syntax_Syntax.mk_Tm_app t_v
                                    (FStar_List.append args_sol_s args)
                                    FStar_Pervasives_Native.None
                                    t0.FStar_Syntax_Syntax.pos
                                   in
                                (t, wl1))))))
           | uu____4939 ->
               failwith "ensure_no_uvar_subst: expected a uvar at the head")
  
let (destruct_flex_t' : FStar_Syntax_Syntax.term -> flex_t) =
  fun t  ->
    let uu____4951 = FStar_Syntax_Util.head_and_args t  in
    match uu____4951 with
    | (head,args) ->
        let uu____4994 =
          let uu____4995 = FStar_Syntax_Subst.compress head  in
          uu____4995.FStar_Syntax_Syntax.n  in
        (match uu____4994 with
         | FStar_Syntax_Syntax.Tm_uvar (uv,s) -> (t, uv, args)
         | uu____5016 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term -> worklist -> (flex_t * worklist)) =
  fun t  ->
    fun wl  ->
      let uu____5037 = ensure_no_uvar_subst t wl  in
      match uu____5037 with
      | (t1,wl1) ->
          let uu____5048 = destruct_flex_t' t1  in (uu____5048, wl1)
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____5065 =
          let uu____5088 =
            let uu____5089 = FStar_Syntax_Subst.compress k  in
            uu____5089.FStar_Syntax_Syntax.n  in
          match uu____5088 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5171 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5171)
              else
                (let uu____5206 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5206 with
                 | (ys',t1,uu____5239) ->
                     let uu____5244 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5244))
          | uu____5283 ->
              let uu____5284 =
                let uu____5289 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5289)  in
              ((ys, t), uu____5284)
           in
        match uu____5065 with
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
                 let uu____5384 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5384 c  in
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
               (let uu____5462 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5462
                then
                  let uu____5467 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5469 = print_ctx_uvar uv  in
                  let uu____5471 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5467 uu____5469 uu____5471
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5480 =
                   let uu____5482 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5482  in
                 let uu____5485 =
                   let uu____5488 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5488
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5480 uu____5485 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail uu____5521 =
               let uu____5522 =
                 let uu____5524 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5526 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5524 uu____5526
                  in
               failwith uu____5522  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5592  ->
                       match uu____5592 with
                       | (a,i) ->
                           let uu____5613 =
                             let uu____5614 = FStar_Syntax_Subst.compress a
                                in
                             uu____5614.FStar_Syntax_Syntax.n  in
                           (match uu____5613 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5640 -> (fail (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5650 =
                 let uu____5652 = is_flex g  in Prims.op_Negation uu____5652
                  in
               if uu____5650
               then (if resolve_ok then wl else (fail (); wl))
               else
                 (let uu____5661 = destruct_flex_t g wl  in
                  match uu____5661 with
                  | ((uu____5666,uv1,args),wl1) ->
                      ((let uu____5671 = args_as_binders args  in
                        assign_solution uu____5671 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___734_5673 = wl1  in
              {
                attempting = (uu___734_5673.attempting);
                wl_deferred = (uu___734_5673.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___734_5673.defer_ok);
                smt_ok = (uu___734_5673.smt_ok);
                umax_heuristic_ok = (uu___734_5673.umax_heuristic_ok);
                tcenv = (uu___734_5673.tcenv);
                wl_implicits = (uu___734_5673.wl_implicits);
                repr_subcomp_allowed = (uu___734_5673.repr_subcomp_allowed)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5698 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5698
         then
           let uu____5703 = FStar_Util.string_of_int pid  in
           let uu____5705 = uvis_to_string wl.tcenv sol  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5703 uu____5705
         else ());
        commit sol;
        (let uu___742_5711 = wl  in
         {
           attempting = (uu___742_5711.attempting);
           wl_deferred = (uu___742_5711.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___742_5711.defer_ok);
           smt_ok = (uu___742_5711.smt_ok);
           umax_heuristic_ok = (uu___742_5711.umax_heuristic_ok);
           tcenv = (uu___742_5711.tcenv);
           wl_implicits = (uu___742_5711.wl_implicits);
           repr_subcomp_allowed = (uu___742_5711.repr_subcomp_allowed)
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
          (let uu____5747 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____5747
           then
             let uu____5752 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____5756 = uvis_to_string wl.tcenv uvis  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5752 uu____5756
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk  ->
    fun t  ->
      let uvars =
        let uu____5783 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5783 FStar_Util.set_elements  in
      let occurs =
        FStar_All.pipe_right uvars
          (FStar_Util.for_some
             (fun uv  ->
                FStar_Syntax_Unionfind.equiv
                  uv.FStar_Syntax_Syntax.ctx_uvar_head
                  uk.FStar_Syntax_Syntax.ctx_uvar_head))
         in
      (uvars, occurs)
  
let (occurs_check :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool * Prims.string
        FStar_Pervasives_Native.option))
  =
  fun uk  ->
    fun t  ->
      let uu____5823 = occurs uk t  in
      match uu____5823 with
      | (uvars,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5862 =
                 let uu____5864 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5866 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5864 uu____5866
                  in
               FStar_Pervasives_Native.Some uu____5862)
             in
          (uvars, (Prims.op_Negation occurs1), msg)
  
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
          let uu____5977 = FStar_Syntax_Syntax.bv_eq b b'  in
          if uu____5977
          then
            let uu____5988 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5988 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____6039 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6096  ->
             match uu____6096 with
             | (x,uu____6108) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6126 = FStar_List.last bs  in
      match uu____6126 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6150) ->
          let uu____6161 =
            FStar_Util.prefix_until
              (fun uu___18_6176  ->
                 match uu___18_6176 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6179 -> false) g
             in
          (match uu____6161 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6193,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6230 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6230 with
        | (pfx,uu____6240) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6252 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6252 with
             | (uu____6260,src',wl1) ->
                 (FStar_Syntax_Util.set_uvar
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
        let as_set v =
          FStar_All.pipe_right v
            (FStar_List.fold_left
               (fun out  ->
                  fun x  ->
                    FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
               FStar_Syntax_Syntax.no_names)
           in
        let v1_set = as_set v1  in
        let ctx_binders =
          FStar_List.fold_left
            (fun out  ->
               fun b  ->
                 match b with
                 | FStar_Syntax_Syntax.Binding_var x ->
                     FStar_Util.set_add x out
                 | uu____6374 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6375 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6439  ->
                  fun uu____6440  ->
                    match (uu____6439, uu____6440) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6543 =
                          let uu____6545 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6545
                           in
                        if uu____6543
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6579 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6579
                           then
                             let uu____6596 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6596)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6375 with | (isect,uu____6646) -> FStar_List.rev isect
  
let binders_eq :
  'uuuuuu6682 'uuuuuu6683 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu6682) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6683) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6741  ->
              fun uu____6742  ->
                match (uu____6741, uu____6742) with
                | ((a,uu____6761),(b,uu____6763)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'uuuuuu6779 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6779) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6810  ->
           match uu____6810 with
           | (y,uu____6817) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'uuuuuu6827 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6827) Prims.list ->
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
              let hd = sn env arg  in
              (match hd.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_name a ->
                   let uu____6989 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6989
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____7022 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7074 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7118 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7139 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_7147  ->
    match uu___19_7147 with
    | MisMatch (d1,d2) ->
        let uu____7159 =
          let uu____7161 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7163 =
            let uu____7165 =
              let uu____7167 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7167 ")"  in
            Prims.op_Hat ") (" uu____7165  in
          Prims.op_Hat uu____7161 uu____7163  in
        Prims.op_Hat "MisMatch (" uu____7159
    | HeadMatch u ->
        let uu____7174 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7174
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___20_7183  ->
    match uu___20_7183 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7200 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv  in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____7215 =
            (let uu____7221 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule
                in
             let uu____7223 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             uu____7221 = uu____7223) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
             in
          if uu____7215 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7232 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7232 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7243 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7267 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7277 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7296 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7296
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7297 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7298 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7299 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7312 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7326 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7350) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7356,uu____7357) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7399) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7424;
             FStar_Syntax_Syntax.index = uu____7425;
             FStar_Syntax_Syntax.sort = t2;_},uu____7427)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7435 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7436 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7437 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7452 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7459 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7479 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7479
  
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
           { FStar_Syntax_Syntax.blob = uu____7498;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7499;
             FStar_Syntax_Syntax.ltyp = uu____7500;
             FStar_Syntax_Syntax.rng = uu____7501;_},uu____7502)
            ->
            let uu____7513 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7513 t21
        | (uu____7514,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7515;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7516;
             FStar_Syntax_Syntax.ltyp = uu____7517;
             FStar_Syntax_Syntax.rng = uu____7518;_})
            ->
            let uu____7529 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7529
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7532 = FStar_Syntax_Syntax.bv_eq x y  in
            if uu____7532
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7543 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7543
            then FullMatch
            else
              (let uu____7548 =
                 let uu____7557 =
                   let uu____7560 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7560  in
                 let uu____7561 =
                   let uu____7564 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7564  in
                 (uu____7557, uu____7561)  in
               MisMatch uu____7548)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7570),FStar_Syntax_Syntax.Tm_uinst (g,uu____7572)) ->
            let uu____7581 = head_matches env f g  in
            FStar_All.pipe_right uu____7581 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7582) -> HeadMatch true
        | (uu____7584,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7588 = FStar_Const.eq_const c d  in
            if uu____7588
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7598),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7600)) ->
            let uu____7633 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7633
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7643),FStar_Syntax_Syntax.Tm_refine (y,uu____7645)) ->
            let uu____7654 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7654 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7656),uu____7657) ->
            let uu____7662 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7662 head_match
        | (uu____7663,FStar_Syntax_Syntax.Tm_refine (x,uu____7665)) ->
            let uu____7670 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7670 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7671,FStar_Syntax_Syntax.Tm_type
           uu____7672) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7674,FStar_Syntax_Syntax.Tm_arrow uu____7675) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head,uu____7706),FStar_Syntax_Syntax.Tm_app (head',uu____7708))
            ->
            let uu____7757 = head_matches env head head'  in
            FStar_All.pipe_right uu____7757 head_match
        | (FStar_Syntax_Syntax.Tm_app (head,uu____7759),uu____7760) ->
            let uu____7785 = head_matches env head t21  in
            FStar_All.pipe_right uu____7785 head_match
        | (uu____7786,FStar_Syntax_Syntax.Tm_app (head,uu____7788)) ->
            let uu____7813 = head_matches env t11 head  in
            FStar_All.pipe_right uu____7813 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7814,FStar_Syntax_Syntax.Tm_let
           uu____7815) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7843,FStar_Syntax_Syntax.Tm_match uu____7844) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7890,FStar_Syntax_Syntax.Tm_abs
           uu____7891) -> HeadMatch true
        | uu____7929 ->
            let uu____7934 =
              let uu____7943 = delta_depth_of_term env t11  in
              let uu____7946 = delta_depth_of_term env t21  in
              (uu____7943, uu____7946)  in
            MisMatch uu____7934
  
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
            let head =
              let uu____8015 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____8015  in
            (let uu____8017 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8017
             then
               let uu____8022 = FStar_Syntax_Print.term_to_string t  in
               let uu____8024 = FStar_Syntax_Print.term_to_string head  in
               FStar_Util.print2 "Head of %s is %s\n" uu____8022 uu____8024
             else ());
            (let uu____8029 =
               let uu____8030 = FStar_Syntax_Util.un_uinst head  in
               uu____8030.FStar_Syntax_Syntax.n  in
             match uu____8029 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____8036 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____8036 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8050 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____8050
                        then
                          let uu____8055 =
                            FStar_Syntax_Print.term_to_string head  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8055
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8060 ->
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
                      let uu____8078 =
                        let uu____8080 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8080 = FStar_Syntax_Util.Equal  in
                      if uu____8078
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8087 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8087
                          then
                            let uu____8092 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8094 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8092
                              uu____8094
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8099 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            (let uu____8251 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8251
             then
               let uu____8256 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8258 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8260 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8256
                 uu____8258 uu____8260
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8288 =
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
               match uu____8288 with
               | (t12,t22) -> aux retry (n_delta + Prims.int_one) t12 t22  in
             let reduce_both_and_try_again d r1 =
               let uu____8336 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8336 with
               | FStar_Pervasives_Native.None  -> fail n_delta r1 t11 t21
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
                   aux retry (n_delta + Prims.int_one) t12 t22
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
                  uu____8374),uu____8375)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8396 =
                      let uu____8405 = maybe_inline t11  in
                      let uu____8408 = maybe_inline t21  in
                      (uu____8405, uu____8408)  in
                    match uu____8396 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail n_delta r t11 t21
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
                 (uu____8451,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8452))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8473 =
                      let uu____8482 = maybe_inline t11  in
                      let uu____8485 = maybe_inline t21  in
                      (uu____8482, uu____8485)  in
                    match uu____8473 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail n_delta r t11 t21
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
             | MisMatch uu____8540 -> fail n_delta r t11 t21
             | uu____8549 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8564 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8564
           then
             let uu____8569 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8571 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8573 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8581 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8598 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8598
                    (fun uu____8633  ->
                       match uu____8633 with
                       | (t11,t21) ->
                           let uu____8641 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8643 =
                             let uu____8645 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8645  in
                           Prims.op_Hat uu____8641 uu____8643))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8569 uu____8571 uu____8573 uu____8581
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8662 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8662 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_8677  ->
    match uu___21_8677 with
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
      let uu___1231_8726 = p  in
      let uu____8729 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8730 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1231_8726.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8729;
        FStar_TypeChecker_Common.relation =
          (uu___1231_8726.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8730;
        FStar_TypeChecker_Common.element =
          (uu___1231_8726.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1231_8726.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1231_8726.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1231_8726.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1231_8726.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1231_8726.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8745 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8745
            (fun uu____8750  -> FStar_TypeChecker_Common.TProb uu____8750)
      | FStar_TypeChecker_Common.CProb uu____8751 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8774 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8774 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8782 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8782 with
           | (lh,lhs_args) ->
               let uu____8829 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8829 with
                | (rh,rhs_args) ->
                    let uu____8876 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8889,FStar_Syntax_Syntax.Tm_uvar uu____8890)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8979 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9006,uu____9007)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9022,FStar_Syntax_Syntax.Tm_uvar uu____9023)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9038,FStar_Syntax_Syntax.Tm_arrow uu____9039)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1282_9069 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1282_9069.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1282_9069.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1282_9069.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1282_9069.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1282_9069.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1282_9069.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1282_9069.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1282_9069.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1282_9069.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9072,FStar_Syntax_Syntax.Tm_type uu____9073)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1282_9089 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1282_9089.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1282_9089.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1282_9089.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1282_9089.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1282_9089.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1282_9089.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1282_9089.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1282_9089.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1282_9089.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9092,FStar_Syntax_Syntax.Tm_uvar uu____9093)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1282_9109 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1282_9109.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1282_9109.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1282_9109.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1282_9109.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1282_9109.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1282_9109.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1282_9109.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1282_9109.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1282_9109.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9112,FStar_Syntax_Syntax.Tm_uvar uu____9113)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9128,uu____9129)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9144,FStar_Syntax_Syntax.Tm_uvar uu____9145)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9160,uu____9161) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8876 with
                     | (rank,tp1) ->
                         let uu____9174 =
                           FStar_All.pipe_right
                             (let uu___1302_9178 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1302_9178.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1302_9178.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1302_9178.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1302_9178.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1302_9178.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1302_9178.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1302_9178.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1302_9178.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1302_9178.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____9181  ->
                                FStar_TypeChecker_Common.TProb uu____9181)
                            in
                         (rank, uu____9174))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9185 =
            FStar_All.pipe_right
              (let uu___1306_9189 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1306_9189.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1306_9189.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1306_9189.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1306_9189.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1306_9189.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1306_9189.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1306_9189.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1306_9189.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1306_9189.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____9192  -> FStar_TypeChecker_Common.CProb uu____9192)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9185)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9252 probs =
      match uu____9252 with
      | (min_rank,min,out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9333 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____9354 = rank wl.tcenv hd  in
               (match uu____9354 with
                | (rank1,hd1) ->
                    if rank_leq rank1 FStar_TypeChecker_Common.Flex_rigid_eq
                    then
                      (match min with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.Some
                             (hd1, (FStar_List.append out tl), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           FStar_Pervasives_Native.Some
                             (hd1, (FStar_List.append out (m :: tl)), rank1))
                    else
                      (let uu____9415 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9420 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9420)
                          in
                       if uu____9415
                       then
                         match min with
                         | FStar_Pervasives_Native.None  ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd1), out) tl
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd1), (m ::
                                 out)) tl
                       else aux (min_rank, min, (hd1 :: out)) tl)))
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
          let uu____9493 = FStar_Syntax_Util.head_and_args t  in
          match uu____9493 with
          | (hd,uu____9512) ->
              let uu____9537 =
                let uu____9538 = FStar_Syntax_Subst.compress hd  in
                uu____9538.FStar_Syntax_Syntax.n  in
              (match uu____9537 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9543) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9578  ->
                           match uu____9578 with
                           | (y,uu____9587) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9610  ->
                                       match uu____9610 with
                                       | (x,uu____9619) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9624 -> false)
           in
        let uu____9626 = rank tcenv p  in
        match uu____9626 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9635 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9716 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9735 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9754 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9771 = FStar_Thunk.mkv s  in UFailed uu____9771 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9786 = mklstr s  in UFailed uu____9786 
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
                        let uu____9837 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9837 with
                        | (k,uu____9845) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9860 -> false)))
            | uu____9862 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9914 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  FStar_Syntax_Util.eq_univs uv1 uv2))
                           in
                        if uu____9914 then uv1 :: uvs else uvs) [])
               in
            let filter =
              FStar_List.filter
                (fun u  ->
                   let uu____9938 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  -> FStar_Syntax_Util.eq_univs u u'))
                      in
                   Prims.op_Negation uu____9938)
               in
            let uu____9945 = filter u12  in
            let uu____9948 = filter u22  in (uu____9945, uu____9948)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9983 = filter_out_common_univs us1 us2  in
                   (match uu____9983 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____10043 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____10043 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10046 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10063  ->
                               let uu____10064 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10066 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10064 uu____10066))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10092 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10092 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10118 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10118 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10121 ->
                   ufailed_thunk
                     (fun uu____10132  ->
                        let uu____10133 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10135 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10133 uu____10135 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10138,uu____10139) ->
              let uu____10141 =
                let uu____10143 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10145 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10143 uu____10145
                 in
              failwith uu____10141
          | (FStar_Syntax_Syntax.U_unknown ,uu____10148) ->
              let uu____10149 =
                let uu____10151 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10153 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10151 uu____10153
                 in
              failwith uu____10149
          | (uu____10156,FStar_Syntax_Syntax.U_bvar uu____10157) ->
              let uu____10159 =
                let uu____10161 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10163 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10161 uu____10163
                 in
              failwith uu____10159
          | (uu____10166,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10167 =
                let uu____10169 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10171 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10169 uu____10171
                 in
              failwith uu____10167
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              let uu____10176 =
                let uu____10178 = FStar_Ident.text_of_id x  in
                let uu____10180 = FStar_Ident.text_of_id y  in
                uu____10178 = uu____10180  in
              if uu____10176
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10211 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10211
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10230 = occurs_univ v1 u3  in
              if uu____10230
              then
                let uu____10233 =
                  let uu____10235 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10237 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10235 uu____10237
                   in
                try_umax_components u11 u21 uu____10233
              else
                (let uu____10242 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10242)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10256 = occurs_univ v1 u3  in
              if uu____10256
              then
                let uu____10259 =
                  let uu____10261 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10263 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10261 uu____10263
                   in
                try_umax_components u11 u21 uu____10259
              else
                (let uu____10268 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10268)
          | (FStar_Syntax_Syntax.U_max uu____10269,uu____10270) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10278 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10278
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10284,FStar_Syntax_Syntax.U_max uu____10285) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10293 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10293
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10299,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10301,FStar_Syntax_Syntax.U_name uu____10302) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10304) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10306) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10308,FStar_Syntax_Syntax.U_succ uu____10309) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10311,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10418 = bc1  in
      match uu____10418 with
      | (bs1,mk_cod1) ->
          let uu____10462 = bc2  in
          (match uu____10462 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10573 = aux xs ys  in
                     (match uu____10573 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10656 =
                       let uu____10663 = mk_cod1 xs  in ([], uu____10663)  in
                     let uu____10666 =
                       let uu____10673 = mk_cod2 ys  in ([], uu____10673)  in
                     (uu____10656, uu____10666)
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
                  let uu____10742 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10742 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10745 =
                    let uu____10746 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10746 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10745
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10751 = has_type_guard t1 t2  in (uu____10751, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10752 = has_type_guard t2 t1  in (uu____10752, wl)
  
let is_flex_pat :
  'uuuuuu10762 'uuuuuu10763 'uuuuuu10764 .
    ('uuuuuu10762 * 'uuuuuu10763 * 'uuuuuu10764 Prims.list) -> Prims.bool
  =
  fun uu___22_10778  ->
    match uu___22_10778 with
    | (uu____10787,uu____10788,[]) -> true
    | uu____10792 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10825 = f  in
      match uu____10825 with
      | (uu____10832,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10833;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10834;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10837;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10838;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10839;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10840;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10912  ->
                 match uu____10912 with
                 | (y,uu____10921) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11075 =
                  let uu____11090 =
                    let uu____11093 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11093  in
                  ((FStar_List.rev pat_binders), uu____11090)  in
                FStar_Pervasives_Native.Some uu____11075
            | (uu____11126,[]) ->
                let uu____11157 =
                  let uu____11172 =
                    let uu____11175 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11175  in
                  ((FStar_List.rev pat_binders), uu____11172)  in
                FStar_Pervasives_Native.Some uu____11157
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11266 =
                  let uu____11267 = FStar_Syntax_Subst.compress a  in
                  uu____11267.FStar_Syntax_Syntax.n  in
                (match uu____11266 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11287 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11287
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1634_11317 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1634_11317.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1634_11317.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst =
                          let uu____11321 =
                            let uu____11322 =
                              let uu____11329 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11329)  in
                            FStar_Syntax_Syntax.NT uu____11322  in
                          [uu____11321]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1  in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res  in
                        aux
                          (((let uu___1640_11345 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1640_11345.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1640_11345.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11346 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11386 =
                  let uu____11393 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11393  in
                (match uu____11386 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11452 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11477 ->
               let uu____11478 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11478 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11774 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11774
       then
         let uu____11779 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11779
       else ());
      (let uu____11785 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____11785
       then
         let uu____11790 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11790
       else ());
      (let uu____11795 = next_prob probs  in
       match uu____11795 with
       | FStar_Pervasives_Native.Some (hd,tl,rank1) ->
           let probs1 =
             let uu___1667_11822 = probs  in
             {
               attempting = tl;
               wl_deferred = (uu___1667_11822.wl_deferred);
               ctr = (uu___1667_11822.ctr);
               defer_ok = (uu___1667_11822.defer_ok);
               smt_ok = (uu___1667_11822.smt_ok);
               umax_heuristic_ok = (uu___1667_11822.umax_heuristic_ok);
               tcenv = (uu___1667_11822.tcenv);
               wl_implicits = (uu___1667_11822.wl_implicits);
               repr_subcomp_allowed = (uu___1667_11822.repr_subcomp_allowed)
             }  in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11831 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11831
                 then
                   let uu____11834 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1  in
                   solve env uu____11834
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
                       (let uu____11841 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd
                            probs1
                           in
                        solve env uu____11841)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1679_11847 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1679_11847.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1679_11847.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1679_11847.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1679_11847.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1679_11847.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1679_11847.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1679_11847.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1679_11847.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1679_11847.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11872 ->
                let uu____11882 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11947  ->
                          match uu____11947 with
                          | (c,uu____11957,uu____11958) -> c < probs.ctr))
                   in
                (match uu____11882 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____12006 =
                            let uu____12011 =
                              FStar_List.map
                                (fun uu____12032  ->
                                   match uu____12032 with
                                   | (uu____12048,x,y) ->
                                       let uu____12059 = FStar_Thunk.force x
                                          in
                                       (uu____12059, y)) probs.wl_deferred
                               in
                            (uu____12011, (probs.wl_implicits))  in
                          Success uu____12006
                      | uu____12063 ->
                          let uu____12073 =
                            let uu___1697_12074 = probs  in
                            let uu____12075 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12096  ->
                                      match uu____12096 with
                                      | (uu____12104,uu____12105,y) -> y))
                               in
                            {
                              attempting = uu____12075;
                              wl_deferred = rest;
                              ctr = (uu___1697_12074.ctr);
                              defer_ok = (uu___1697_12074.defer_ok);
                              smt_ok = (uu___1697_12074.smt_ok);
                              umax_heuristic_ok =
                                (uu___1697_12074.umax_heuristic_ok);
                              tcenv = (uu___1697_12074.tcenv);
                              wl_implicits = (uu___1697_12074.wl_implicits);
                              repr_subcomp_allowed =
                                (uu___1697_12074.repr_subcomp_allowed)
                            }  in
                          solve env uu____12073))))

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
            let uu____12114 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12114 with
            | USolved wl1 ->
                let uu____12116 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12116
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12119 = defer_lit "" orig wl1  in
                solve env uu____12119

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
                  let uu____12170 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12170 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12173 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12186;
                  FStar_Syntax_Syntax.vars = uu____12187;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12190;
                  FStar_Syntax_Syntax.vars = uu____12191;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12204,uu____12205) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12213,FStar_Syntax_Syntax.Tm_uinst uu____12214) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12222 -> USolved wl

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
            ((let uu____12233 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12233
              then
                let uu____12238 = prob_to_string env orig  in
                let uu____12240 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12238 uu____12240
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
               let uu____12333 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12333 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12388 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12388
                then
                  let uu____12393 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12395 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12393 uu____12395
                else ());
               (let uu____12400 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12400 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12446 = eq_prob t1 t2 wl2  in
                         (match uu____12446 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12467 ->
                         let uu____12476 = eq_prob t1 t2 wl2  in
                         (match uu____12476 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12526 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12541 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12542 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12541, uu____12542)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12547 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12548 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12547, uu____12548)
                            in
                         (match uu____12526 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12579 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12579 with
                                | (t1_hd,t1_args) ->
                                    let uu____12624 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12624 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12690 =
                                              let uu____12697 =
                                                let uu____12708 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12708 :: t1_args  in
                                              let uu____12725 =
                                                let uu____12734 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12734 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12783  ->
                                                   fun uu____12784  ->
                                                     fun uu____12785  ->
                                                       match (uu____12783,
                                                               uu____12784,
                                                               uu____12785)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12835),
                                                          (a2,uu____12837))
                                                           ->
                                                           let uu____12874 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12874
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12697
                                                uu____12725
                                               in
                                            match uu____12690 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1851_12900 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1851_12900.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1851_12900.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1851_12900.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1851_12900.repr_subcomp_allowed)
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12911 =
                                                  solve env1 wl'  in
                                                (match uu____12911 with
                                                 | Success (uu____12914,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1860_12918
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1860_12918.attempting);
                                                            wl_deferred =
                                                              (uu___1860_12918.wl_deferred);
                                                            ctr =
                                                              (uu___1860_12918.ctr);
                                                            defer_ok =
                                                              (uu___1860_12918.defer_ok);
                                                            smt_ok =
                                                              (uu___1860_12918.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1860_12918.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1860_12918.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps);
                                                            repr_subcomp_allowed
                                                              =
                                                              (uu___1860_12918.repr_subcomp_allowed)
                                                          })))
                                                 | Failed uu____12919 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12951 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12951 with
                                | (t1_base,p1_opt) ->
                                    let uu____12987 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12987 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____13086 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13086
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
                                               let subst =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi11 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi1
                                                  in
                                               let phi21 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi2
                                                  in
                                               let uu____13139 =
                                                 op phi11 phi21  in
                                               refine x1 uu____13139
                                           | (FStar_Pervasives_Native.None
                                              ,FStar_Pervasives_Native.Some
                                              (x,phi)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi
                                                  in
                                               let uu____13171 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13171
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi),FStar_Pervasives_Native.None
                                              ) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi
                                                  in
                                               let uu____13203 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13203
                                           | uu____13206 -> t_base  in
                                         let uu____13223 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13223 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13237 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13237, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13244 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13244 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13280 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13280 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13316 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13316
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
                              let uu____13340 = combine t11 t21 wl2  in
                              (match uu____13340 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13373 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13373
                                     then
                                       let uu____13378 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13378
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13420 ts1 =
               match uu____13420 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13483 = pairwise out t wl2  in
                        (match uu____13483 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13519 =
               let uu____13530 = FStar_List.hd ts  in (uu____13530, [], wl1)
                in
             let uu____13539 = FStar_List.tl ts  in
             aux uu____13519 uu____13539  in
           let uu____13546 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13546 with
           | (this_flex,this_rigid) ->
               let uu____13572 =
                 let uu____13573 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13573.FStar_Syntax_Syntax.n  in
               (match uu____13572 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13598 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13598
                    then
                      let uu____13601 = destruct_flex_t this_flex wl  in
                      (match uu____13601 with
                       | (flex,wl1) ->
                           let uu____13608 = quasi_pattern env flex  in
                           (match uu____13608 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t1)
                                ->
                                ((let uu____13627 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13627
                                  then
                                    let uu____13632 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13632
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13639 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1962_13642 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1962_13642.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1962_13642.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1962_13642.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1962_13642.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1962_13642.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1962_13642.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1962_13642.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1962_13642.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1962_13642.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13639)
                | uu____13643 ->
                    ((let uu____13645 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13645
                      then
                        let uu____13650 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13650
                      else ());
                     (let uu____13655 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13655 with
                      | (u,_args) ->
                          let uu____13698 =
                            let uu____13699 = FStar_Syntax_Subst.compress u
                               in
                            uu____13699.FStar_Syntax_Syntax.n  in
                          (match uu____13698 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv t =
                                 let uu____13727 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13727 with
                                 | (u',uu____13746) ->
                                     let uu____13771 =
                                       let uu____13772 = whnf env u'  in
                                       uu____13772.FStar_Syntax_Syntax.n  in
                                     (match uu____13771 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13794 -> false)
                                  in
                               let uu____13796 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_13819  ->
                                         match uu___23_13819 with
                                         | FStar_TypeChecker_Common.TProb tp1
                                             ->
                                             let tp2 = maybe_invert tp1  in
                                             (match tp2.FStar_TypeChecker_Common.rank
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  rank' when rank1 = rank' ->
                                                  if flip
                                                  then
                                                    equiv
                                                      tp2.FStar_TypeChecker_Common.lhs
                                                  else
                                                    equiv
                                                      tp2.FStar_TypeChecker_Common.rhs
                                              | uu____13833 -> false)
                                         | uu____13837 -> false))
                                  in
                               (match uu____13796 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13852 = whnf env this_rigid
                                         in
                                      let uu____13853 =
                                        FStar_List.collect
                                          (fun uu___24_13859  ->
                                             match uu___24_13859 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13865 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13865]
                                             | uu____13869 -> [])
                                          bounds_probs
                                         in
                                      uu____13852 :: uu____13853  in
                                    let uu____13870 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13870 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13903 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13918 =
                                               let uu____13919 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13919.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13918 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13931 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13931)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13942 -> bound  in
                                           let uu____13943 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13943)  in
                                         (match uu____13903 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13978 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13978
                                                then
                                                  let wl'1 =
                                                    let uu___2022_13984 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2022_13984.wl_deferred);
                                                      ctr =
                                                        (uu___2022_13984.ctr);
                                                      defer_ok =
                                                        (uu___2022_13984.defer_ok);
                                                      smt_ok =
                                                        (uu___2022_13984.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2022_13984.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2022_13984.tcenv);
                                                      wl_implicits =
                                                        (uu___2022_13984.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2022_13984.repr_subcomp_allowed)
                                                    }  in
                                                  let uu____13985 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13985
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13991 =
                                                  solve_t env eq_prob
                                                    (let uu___2027_13993 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2027_13993.wl_deferred);
                                                       ctr =
                                                         (uu___2027_13993.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2027_13993.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2027_13993.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2027_13993.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2027_13993.repr_subcomp_allowed)
                                                     })
                                                   in
                                                match uu____13991 with
                                                | Success (uu____13995,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2033_13998 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2033_13998.wl_deferred);
                                                        ctr =
                                                          (uu___2033_13998.ctr);
                                                        defer_ok =
                                                          (uu___2033_13998.defer_ok);
                                                        smt_ok =
                                                          (uu___2033_13998.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2033_13998.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2033_13998.tcenv);
                                                        wl_implicits =
                                                          (uu___2033_13998.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2033_13998.repr_subcomp_allowed)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2036_14000 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2036_14000.attempting);
                                                        wl_deferred =
                                                          (uu___2036_14000.wl_deferred);
                                                        ctr =
                                                          (uu___2036_14000.ctr);
                                                        defer_ok =
                                                          (uu___2036_14000.defer_ok);
                                                        smt_ok =
                                                          (uu___2036_14000.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2036_14000.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2036_14000.tcenv);
                                                        wl_implicits =
                                                          (FStar_List.append
                                                             wl'.wl_implicits
                                                             imps);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2036_14000.repr_subcomp_allowed)
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
                                                    let uu____14016 =
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
                                                    ((let uu____14028 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____14028
                                                      then
                                                        let uu____14033 =
                                                          let uu____14035 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____14035
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14033
                                                      else ());
                                                     (let uu____14048 =
                                                        let uu____14063 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14063)
                                                         in
                                                      match uu____14048 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14085))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14111 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14111
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
                                                                  let uu____14131
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14131))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14156 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14156
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
                                                                    let uu____14176
                                                                    =
                                                                    let uu____14181
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14181
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14176
                                                                    [] wl2
                                                                     in
                                                                  let uu____14187
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14187))))
                                                      | uu____14188 ->
                                                          let uu____14203 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14203 p)))))))
                           | uu____14210 when flip ->
                               let uu____14211 =
                                 let uu____14213 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14215 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14213 uu____14215
                                  in
                               failwith uu____14211
                           | uu____14218 ->
                               let uu____14219 =
                                 let uu____14221 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14223 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14221 uu____14223
                                  in
                               failwith uu____14219)))))

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
                fun arrow  ->
                  let bs_lhs_args =
                    FStar_List.map
                      (fun uu____14259  ->
                         match uu____14259 with
                         | (x,i) ->
                             let uu____14278 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14278, i)) bs_lhs
                     in
                  let uu____14281 = lhs  in
                  match uu____14281 with
                  | (uu____14282,u_lhs,uu____14284) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14381 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14391 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14391, univ)
                             in
                          match uu____14381 with
                          | (k,univ) ->
                              let uu____14398 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14398 with
                               | (uu____14415,u,wl3) ->
                                   let uu____14418 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14418, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14444 =
                              let uu____14457 =
                                let uu____14468 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14468 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14519  ->
                                   fun uu____14520  ->
                                     match (uu____14519, uu____14520) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14621 =
                                           let uu____14628 =
                                             let uu____14631 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14631
                                              in
                                           copy_uvar u_lhs [] uu____14628 wl2
                                            in
                                         (match uu____14621 with
                                          | (uu____14660,t_a,wl3) ->
                                              let uu____14663 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14663 with
                                               | (uu____14682,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14457
                                ([], wl1)
                               in
                            (match uu____14444 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2147_14738 = ct  in
                                   let uu____14739 =
                                     let uu____14742 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14742
                                      in
                                   let uu____14757 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2147_14738.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2147_14738.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14739;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14757;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2147_14738.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2150_14775 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2150_14775.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2150_14775.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14778 =
                        FStar_Syntax_Util.arrow_formals_comp arrow  in
                      (match uu____14778 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14816 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14816 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14827 =
                                          let uu____14832 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14832)  in
                                        TERM uu____14827  in
                                      let uu____14833 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14833 with
                                       | (sub_prob,wl3) ->
                                           let uu____14847 =
                                             let uu____14848 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14848
                                              in
                                           solve env uu____14847))
                             | (x,imp)::formals2 ->
                                 let uu____14870 =
                                   let uu____14877 =
                                     let uu____14880 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14880
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14877 wl1
                                    in
                                 (match uu____14870 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14901 =
                                          let uu____14904 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14904
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14901 u_x
                                         in
                                      let uu____14905 =
                                        let uu____14908 =
                                          let uu____14911 =
                                            let uu____14912 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14912, imp)  in
                                          [uu____14911]  in
                                        FStar_List.append bs_terms
                                          uu____14908
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14905 formals2 wl2)
                              in
                           let uu____14939 = occurs_check u_lhs arrow  in
                           (match uu____14939 with
                            | (uu____14952,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14968 =
                                    mklstr
                                      (fun uu____14973  ->
                                         let uu____14974 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14974)
                                     in
                                  giveup_or_defer env orig wl uu____14968
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
              (let uu____15007 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____15007
               then
                 let uu____15012 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____15015 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15012 (rel_to_string (p_rel orig)) uu____15015
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15146 = rhs wl1 scope env1 subst  in
                     (match uu____15146 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15169 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15169
                            then
                              let uu____15174 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15174
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15252 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15252 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2220_15254 = hd1  in
                       let uu____15255 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2220_15254.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2220_15254.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15255
                       }  in
                     let hd21 =
                       let uu___2223_15259 = hd2  in
                       let uu____15260 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2223_15259.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2223_15259.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15260
                       }  in
                     let uu____15263 =
                       let uu____15268 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15268
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15263 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst1 =
                            let uu____15291 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15291
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15298 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1
                             in
                          (match uu____15298 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15370 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15370
                                  in
                               ((let uu____15388 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15388
                                 then
                                   let uu____15393 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15395 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15393
                                     uu____15395
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____15430 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15466 = aux wl [] env [] bs1 bs2  in
               match uu____15466 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15525 = attempt sub_probs wl2  in
                   solve env1 uu____15525)

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
            let uu___2261_15545 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2261_15545.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2261_15545.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2261_15545.repr_subcomp_allowed)
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15557 = try_solve env wl'  in
          match uu____15557 with
          | Success (uu____15558,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2270_15562 = wl  in
                  {
                    attempting = (uu___2270_15562.attempting);
                    wl_deferred = (uu___2270_15562.wl_deferred);
                    ctr = (uu___2270_15562.ctr);
                    defer_ok = (uu___2270_15562.defer_ok);
                    smt_ok = (uu___2270_15562.smt_ok);
                    umax_heuristic_ok = (uu___2270_15562.umax_heuristic_ok);
                    tcenv = (uu___2270_15562.tcenv);
                    wl_implicits = (FStar_List.append wl.wl_implicits imps);
                    repr_subcomp_allowed =
                      (uu___2270_15562.repr_subcomp_allowed)
                  }  in
                solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____15571 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15571 wl)

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
              let uu____15585 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15585 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15619 = lhs1  in
              match uu____15619 with
              | (uu____15622,ctx_u,uu____15624) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15632 ->
                        let uu____15633 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15633 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15682 = quasi_pattern env1 lhs1  in
              match uu____15682 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15716) ->
                  let uu____15721 = lhs1  in
                  (match uu____15721 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15736 = occurs_check ctx_u rhs1  in
                       (match uu____15736 with
                        | (uvars,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15787 =
                                let uu____15795 =
                                  let uu____15797 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15797
                                   in
                                FStar_Util.Inl uu____15795  in
                              (uu____15787, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15825 =
                                 let uu____15827 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15827  in
                               if uu____15825
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15854 =
                                    let uu____15862 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15862  in
                                  let uu____15868 =
                                    restrict_all_uvars ctx_u uvars wl1  in
                                  (uu____15854, uu____15868)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15912 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15912 with
              | (rhs_hd,args) ->
                  let uu____15955 = FStar_Util.prefix args  in
                  (match uu____15955 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____16027 = lhs1  in
                       (match uu____16027 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____16031 =
                              let uu____16042 =
                                let uu____16049 =
                                  let uu____16052 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____16052
                                   in
                                copy_uvar u_lhs [] uu____16049 wl1  in
                              match uu____16042 with
                              | (uu____16079,t_last_arg,wl2) ->
                                  let uu____16082 =
                                    let uu____16089 =
                                      let uu____16090 =
                                        let uu____16099 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____16099]  in
                                      FStar_List.append bs_lhs uu____16090
                                       in
                                    copy_uvar u_lhs uu____16089 t_res_lhs wl2
                                     in
                                  (match uu____16082 with
                                   | (uu____16134,lhs',wl3) ->
                                       let uu____16137 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16137 with
                                        | (uu____16154,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____16031 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16175 =
                                     let uu____16176 =
                                       let uu____16181 =
                                         let uu____16182 =
                                           let uu____16185 =
                                             let uu____16190 =
                                               let uu____16191 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16191]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16190
                                              in
                                           uu____16185
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16182
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16181)  in
                                     TERM uu____16176  in
                                   [uu____16175]  in
                                 let uu____16216 =
                                   let uu____16223 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16223 with
                                   | (p1,wl3) ->
                                       let uu____16243 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16243 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16216 with
                                  | (sub_probs,wl3) ->
                                      let uu____16275 =
                                        let uu____16276 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16276  in
                                      solve env1 uu____16275))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16310 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16310 with
                | (uu____16328,args) ->
                    (match args with | [] -> false | uu____16364 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16383 =
                  let uu____16384 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16384.FStar_Syntax_Syntax.n  in
                match uu____16383 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16388 -> true
                | uu____16404 -> false  in
              let uu____16406 = quasi_pattern env1 lhs1  in
              match uu____16406 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    mklstr
                      (fun uu____16425  ->
                         let uu____16426 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16426)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16435 = is_app rhs1  in
                  if uu____16435
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16440 = is_arrow rhs1  in
                     if uu____16440
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          mklstr
                            (fun uu____16453  ->
                               let uu____16454 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16454)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16458 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16458
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16464 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16464
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16469 = lhs  in
                (match uu____16469 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16473 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16473 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16491 =
                              let uu____16495 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16495
                               in
                            FStar_All.pipe_right uu____16491
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16516 = occurs_check ctx_uv rhs1  in
                          (match uu____16516 with
                           | (uvars,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16545 =
                                   let uu____16546 =
                                     let uu____16548 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16548
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16546
                                    in
                                 giveup_or_defer env orig wl uu____16545
                               else
                                 (let uu____16556 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16556
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars wl  in
                                    let uu____16563 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16563
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         mklstr
                                           (fun uu____16579  ->
                                              let uu____16580 =
                                                names_to_string1 fvs2  in
                                              let uu____16582 =
                                                names_to_string1 fvs1  in
                                              let uu____16584 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16580 uu____16582
                                                uu____16584)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16596 ->
                          if wl.defer_ok
                          then
                            let uu____16600 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16600
                          else
                            (let uu____16605 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16605 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16631 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16631
                             | (FStar_Util.Inl msg,uu____16633) ->
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
                  let uu____16651 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16651
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16657 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16657
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16679 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16679
                else
                  (let uu____16684 =
                     let uu____16701 = quasi_pattern env lhs  in
                     let uu____16708 = quasi_pattern env rhs  in
                     (uu____16701, uu____16708)  in
                   match uu____16684 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16751 = lhs  in
                       (match uu____16751 with
                        | ({ FStar_Syntax_Syntax.n = uu____16752;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16754;_},u_lhs,uu____16756)
                            ->
                            let uu____16759 = rhs  in
                            (match uu____16759 with
                             | (uu____16760,u_rhs,uu____16762) ->
                                 let uu____16763 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16763
                                 then
                                   let uu____16770 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16770
                                 else
                                   (let uu____16773 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16773 with
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
                                        let uu____16805 =
                                          let uu____16812 =
                                            let uu____16815 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16815
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16812
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16805 with
                                         | (uu____16827,w,wl1) ->
                                             let w_app =
                                               let uu____16833 =
                                                 let uu____16838 =
                                                   FStar_List.map
                                                     (fun uu____16849  ->
                                                        match uu____16849
                                                        with
                                                        | (z,uu____16857) ->
                                                            let uu____16862 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16862) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16838
                                                  in
                                               uu____16833
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16864 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16864
                                               then
                                                 let uu____16869 =
                                                   let uu____16873 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16875 =
                                                     let uu____16879 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16881 =
                                                       let uu____16885 =
                                                         term_to_string w  in
                                                       let uu____16887 =
                                                         let uu____16891 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16900 =
                                                           let uu____16904 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16913 =
                                                             let uu____16917
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16917]
                                                              in
                                                           uu____16904 ::
                                                             uu____16913
                                                            in
                                                         uu____16891 ::
                                                           uu____16900
                                                          in
                                                       uu____16885 ::
                                                         uu____16887
                                                        in
                                                     uu____16879 ::
                                                       uu____16881
                                                      in
                                                   uu____16873 :: uu____16875
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16869
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16934 =
                                                     let uu____16939 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16939)  in
                                                   TERM uu____16934  in
                                                 let uu____16940 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16940
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16948 =
                                                        let uu____16953 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16953)
                                                         in
                                                      TERM uu____16948  in
                                                    [s1; s2])
                                                  in
                                               let uu____16954 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16954))))))
                   | uu____16955 ->
                       let uu____16972 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16972)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17026 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____17026
            then
              let uu____17031 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17033 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17035 = FStar_Syntax_Print.term_to_string t2  in
              let uu____17037 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17031 uu____17033 uu____17035 uu____17037
            else ());
           (let uu____17048 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17048 with
            | (head1,args1) ->
                let uu____17091 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17091 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17161 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17161 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17166 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17166)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17187 =
                         mklstr
                           (fun uu____17198  ->
                              let uu____17199 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17201 = args_to_string args1  in
                              let uu____17205 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17207 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17199 uu____17201 uu____17205
                                uu____17207)
                          in
                       giveup env1 uu____17187 orig
                     else
                       (let uu____17214 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17219 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17219 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17214
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2526_17223 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2526_17223.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2526_17223.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2526_17223.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2526_17223.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2526_17223.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2526_17223.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2526_17223.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2526_17223.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17233 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17233
                                    else solve env1 wl2))
                        else
                          (let uu____17238 = base_and_refinement env1 t1  in
                           match uu____17238 with
                           | (base1,refinement1) ->
                               let uu____17263 = base_and_refinement env1 t2
                                  in
                               (match uu____17263 with
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
                                           let uu____17428 =
                                             FStar_List.fold_right
                                               (fun uu____17468  ->
                                                  fun uu____17469  ->
                                                    match (uu____17468,
                                                            uu____17469)
                                                    with
                                                    | (((a1,uu____17521),
                                                        (a2,uu____17523)),
                                                       (probs,wl3)) ->
                                                        let uu____17572 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17572
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17428 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17615 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17615
                                                 then
                                                   let uu____17620 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17620
                                                 else ());
                                                (let uu____17626 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17626
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
                                                    (let uu____17653 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17653 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17669 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17669
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17677 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17677))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17702 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17702 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17718 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17718
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17726 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17726)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17754 =
                                           match uu____17754 with
                                           | (prob,reason) ->
                                               ((let uu____17771 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17771
                                                 then
                                                   let uu____17776 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17778 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____17776 uu____17778
                                                 else ());
                                                (let uu____17784 =
                                                   let uu____17793 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17796 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17793, uu____17796)
                                                    in
                                                 match uu____17784 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17809 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17809 with
                                                      | (head1',uu____17827)
                                                          ->
                                                          let uu____17852 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17852
                                                           with
                                                           | (head2',uu____17870)
                                                               ->
                                                               let uu____17895
                                                                 =
                                                                 let uu____17900
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17901
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17900,
                                                                   uu____17901)
                                                                  in
                                                               (match uu____17895
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17903
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17903
                                                                    then
                                                                    let uu____17908
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17910
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17912
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17914
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17908
                                                                    uu____17910
                                                                    uu____17912
                                                                    uu____17914
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17919
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2614_17927
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2614_17927.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2614_17927.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2614_17927.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2614_17927.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2614_17927.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2614_17927.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2614_17927.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2614_17927.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17929
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17929
                                                                    then
                                                                    let uu____17934
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17934
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17939 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17951 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17951 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17959 =
                                             let uu____17960 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17960.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17959 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17965 -> false  in
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
                                          | uu____17968 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17971 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2634_18007 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2634_18007.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2634_18007.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2634_18007.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2634_18007.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2634_18007.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2634_18007.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2634_18007.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2634_18007.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18083 = destruct_flex_t scrutinee wl1  in
             match uu____18083 with
             | ((_t,uv,_args),wl2) ->
                 let uu____18094 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18094 with
                  | (xs,pat_term,uu____18110,uu____18111) ->
                      let uu____18116 =
                        FStar_List.fold_left
                          (fun uu____18139  ->
                             fun x  ->
                               match uu____18139 with
                               | (subst,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18160 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18160 with
                                    | (uu____18179,u,wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst  in
                                        (subst1, wl4))) ([], wl2) xs
                         in
                      (match uu____18116 with
                       | (subst,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term  in
                           let uu____18200 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18200 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2674_18217 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2674_18217.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2674_18217.umax_heuristic_ok);
                                    tcenv = (uu___2674_18217.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2674_18217.repr_subcomp_allowed)
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18228 = solve env1 wl'  in
                                (match uu____18228 with
                                 | Success (uu____18231,imps) ->
                                     let wl'1 =
                                       let uu___2682_18234 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2682_18234.wl_deferred);
                                         ctr = (uu___2682_18234.ctr);
                                         defer_ok =
                                           (uu___2682_18234.defer_ok);
                                         smt_ok = (uu___2682_18234.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2682_18234.umax_heuristic_ok);
                                         tcenv = (uu___2682_18234.tcenv);
                                         wl_implicits =
                                           (uu___2682_18234.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2682_18234.repr_subcomp_allowed)
                                       }  in
                                     let uu____18235 = solve env1 wl'1  in
                                     (match uu____18235 with
                                      | Success (uu____18238,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2690_18242 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2690_18242.attempting);
                                                 wl_deferred =
                                                   (uu___2690_18242.wl_deferred);
                                                 ctr = (uu___2690_18242.ctr);
                                                 defer_ok =
                                                   (uu___2690_18242.defer_ok);
                                                 smt_ok =
                                                   (uu___2690_18242.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2690_18242.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2690_18242.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'));
                                                 repr_subcomp_allowed =
                                                   (uu___2690_18242.repr_subcomp_allowed)
                                               })))
                                      | Failed uu____18243 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18249 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18272 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18272
                 then
                   let uu____18277 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18279 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18277 uu____18279
                 else ());
                (let uu____18284 =
                   let uu____18305 =
                     let uu____18314 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18314)  in
                   let uu____18321 =
                     let uu____18330 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18330)  in
                   (uu____18305, uu____18321)  in
                 match uu____18284 with
                 | ((uu____18360,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18363;
                                   FStar_Syntax_Syntax.vars = uu____18364;_}),
                    (s,t)) ->
                     let uu____18435 =
                       let uu____18437 = is_flex scrutinee  in
                       Prims.op_Negation uu____18437  in
                     if uu____18435
                     then
                       ((let uu____18448 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18448
                         then
                           let uu____18453 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18453
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18472 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18472
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18487 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18487
                           then
                             let uu____18492 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18494 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18492 uu____18494
                           else ());
                          (let pat_discriminates uu___25_18519 =
                             match uu___25_18519 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18535;
                                  FStar_Syntax_Syntax.p = uu____18536;_},FStar_Pervasives_Native.None
                                ,uu____18537) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18551;
                                  FStar_Syntax_Syntax.p = uu____18552;_},FStar_Pervasives_Native.None
                                ,uu____18553) -> true
                             | uu____18580 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18683 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18683 with
                                       | (uu____18685,uu____18686,t') ->
                                           let uu____18704 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18704 with
                                            | (FullMatch ,uu____18716) ->
                                                true
                                            | (HeadMatch
                                               uu____18730,uu____18731) ->
                                                true
                                            | uu____18746 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18783 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18783
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18794 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18794 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18882,uu____18883) ->
                                       branches1
                                   | uu____19028 -> branches  in
                                 let uu____19083 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19092 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19092 with
                                        | (p,uu____19096,uu____19097) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19126  ->
                                      FStar_Util.Inr uu____19126) uu____19083))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19156 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19156 with
                                | (p,uu____19165,e) ->
                                    ((let uu____19184 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19184
                                      then
                                        let uu____19189 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19191 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19189 uu____19191
                                      else ());
                                     (let uu____19196 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____19211  ->
                                           FStar_Util.Inr uu____19211)
                                        uu____19196)))))
                 | ((s,t),(uu____19214,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19217;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19218;_}))
                     ->
                     let uu____19287 =
                       let uu____19289 = is_flex scrutinee  in
                       Prims.op_Negation uu____19289  in
                     if uu____19287
                     then
                       ((let uu____19300 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19300
                         then
                           let uu____19305 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19305
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19324 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19324
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19339 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19339
                           then
                             let uu____19344 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19346 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19344 uu____19346
                           else ());
                          (let pat_discriminates uu___25_19371 =
                             match uu___25_19371 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19387;
                                  FStar_Syntax_Syntax.p = uu____19388;_},FStar_Pervasives_Native.None
                                ,uu____19389) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19403;
                                  FStar_Syntax_Syntax.p = uu____19404;_},FStar_Pervasives_Native.None
                                ,uu____19405) -> true
                             | uu____19432 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19535 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19535 with
                                       | (uu____19537,uu____19538,t') ->
                                           let uu____19556 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19556 with
                                            | (FullMatch ,uu____19568) ->
                                                true
                                            | (HeadMatch
                                               uu____19582,uu____19583) ->
                                                true
                                            | uu____19598 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19635 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19635
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19646 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19646 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19734,uu____19735) ->
                                       branches1
                                   | uu____19880 -> branches  in
                                 let uu____19935 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19944 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19944 with
                                        | (p,uu____19948,uu____19949) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19978  ->
                                      FStar_Util.Inr uu____19978) uu____19935))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20008 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20008 with
                                | (p,uu____20017,e) ->
                                    ((let uu____20036 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20036
                                      then
                                        let uu____20041 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20043 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20041 uu____20043
                                      else ());
                                     (let uu____20048 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____20063  ->
                                           FStar_Util.Inr uu____20063)
                                        uu____20048)))))
                 | uu____20064 ->
                     ((let uu____20086 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20086
                       then
                         let uu____20091 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20093 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20091 uu____20093
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20139 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20139
            then
              let uu____20144 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20146 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20148 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20150 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20144 uu____20146 uu____20148 uu____20150
            else ());
           (let uu____20155 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20155 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20186,uu____20187) ->
                     let rec may_relate head =
                       let uu____20215 =
                         let uu____20216 = FStar_Syntax_Subst.compress head
                            in
                         uu____20216.FStar_Syntax_Syntax.n  in
                       match uu____20215 with
                       | FStar_Syntax_Syntax.Tm_name uu____20220 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20222 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20247 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20247 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20249 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20252
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20253 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20256,uu____20257) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20299) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20305) ->
                           may_relate t
                       | uu____20310 -> false  in
                     let uu____20312 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20312 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20325 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20325
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20335 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20335
                          then
                            let uu____20338 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20338 with
                             | (guard,wl2) ->
                                 let uu____20345 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20345)
                          else
                            (let uu____20348 =
                               mklstr
                                 (fun uu____20359  ->
                                    let uu____20360 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20362 =
                                      let uu____20364 =
                                        let uu____20368 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20368
                                          (fun x  ->
                                             let uu____20375 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20375)
                                         in
                                      FStar_Util.dflt "" uu____20364  in
                                    let uu____20380 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20382 =
                                      let uu____20384 =
                                        let uu____20388 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20388
                                          (fun x  ->
                                             let uu____20395 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20395)
                                         in
                                      FStar_Util.dflt "" uu____20384  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20360 uu____20362 uu____20380
                                      uu____20382)
                                in
                             giveup env1 uu____20348 orig))
                 | (HeadMatch (true ),uu____20401) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20416 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20416 with
                        | (guard,wl2) ->
                            let uu____20423 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20423)
                     else
                       (let uu____20426 =
                          mklstr
                            (fun uu____20433  ->
                               let uu____20434 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20436 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20434 uu____20436)
                           in
                        giveup env1 uu____20426 orig)
                 | (uu____20439,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2865_20453 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2865_20453.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2865_20453.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2865_20453.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2865_20453.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2865_20453.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2865_20453.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2865_20453.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2865_20453.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20480 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20480
          then
            let uu____20483 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20483
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20489 =
                let uu____20492 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20492  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20489 t1);
             (let uu____20511 =
                let uu____20514 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20514  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20511 t2);
             (let uu____20533 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20533
              then
                let uu____20537 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20539 =
                  let uu____20541 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20543 =
                    let uu____20545 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20545  in
                  Prims.op_Hat uu____20541 uu____20543  in
                let uu____20548 =
                  let uu____20550 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20552 =
                    let uu____20554 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20554  in
                  Prims.op_Hat uu____20550 uu____20552  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20537 uu____20539 uu____20548
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20561,uu____20562) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20578,FStar_Syntax_Syntax.Tm_delayed uu____20579) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20595,uu____20596) ->
                  let uu____20623 =
                    let uu___2896_20624 = problem  in
                    let uu____20625 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2896_20624.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20625;
                      FStar_TypeChecker_Common.relation =
                        (uu___2896_20624.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2896_20624.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2896_20624.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2896_20624.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2896_20624.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2896_20624.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2896_20624.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2896_20624.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20623 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20626,uu____20627) ->
                  let uu____20634 =
                    let uu___2902_20635 = problem  in
                    let uu____20636 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2902_20635.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20636;
                      FStar_TypeChecker_Common.relation =
                        (uu___2902_20635.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2902_20635.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2902_20635.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2902_20635.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2902_20635.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2902_20635.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2902_20635.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2902_20635.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20634 wl
              | (uu____20637,FStar_Syntax_Syntax.Tm_ascribed uu____20638) ->
                  let uu____20665 =
                    let uu___2908_20666 = problem  in
                    let uu____20667 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2908_20666.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2908_20666.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2908_20666.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20667;
                      FStar_TypeChecker_Common.element =
                        (uu___2908_20666.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2908_20666.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2908_20666.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2908_20666.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2908_20666.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2908_20666.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20665 wl
              | (uu____20668,FStar_Syntax_Syntax.Tm_meta uu____20669) ->
                  let uu____20676 =
                    let uu___2914_20677 = problem  in
                    let uu____20678 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2914_20677.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2914_20677.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2914_20677.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20678;
                      FStar_TypeChecker_Common.element =
                        (uu___2914_20677.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2914_20677.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2914_20677.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2914_20677.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2914_20677.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2914_20677.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20676 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20680),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20682)) ->
                  let uu____20691 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20691
              | (FStar_Syntax_Syntax.Tm_bvar uu____20692,uu____20693) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20695,FStar_Syntax_Syntax.Tm_bvar uu____20696) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___26_20766 =
                    match uu___26_20766 with
                    | [] -> c
                    | bs ->
                        let uu____20794 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20794
                     in
                  let uu____20805 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20805 with
                   | ((bs11,c11),(bs21,c21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst  ->
                                  let c12 =
                                    FStar_Syntax_Subst.subst_comp subst c11
                                     in
                                  let c22 =
                                    FStar_Syntax_Subst.subst_comp subst c21
                                     in
                                  let rel =
                                    let uu____20954 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20954
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
                  let mk_t t l uu___27_21043 =
                    match uu___27_21043 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21085 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21085 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst  ->
                                  let uu____21230 =
                                    FStar_Syntax_Subst.subst subst tbody11
                                     in
                                  let uu____21231 =
                                    FStar_Syntax_Subst.subst subst tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21230
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21231 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21233,uu____21234) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21265 -> true
                    | uu____21285 -> false  in
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
                      (let uu____21345 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3016_21353 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3016_21353.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3016_21353.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3016_21353.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3016_21353.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3016_21353.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3016_21353.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3016_21353.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3016_21353.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3016_21353.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3016_21353.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3016_21353.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3016_21353.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3016_21353.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3016_21353.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3016_21353.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3016_21353.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3016_21353.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3016_21353.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3016_21353.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3016_21353.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3016_21353.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3016_21353.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3016_21353.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3016_21353.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3016_21353.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3016_21353.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3016_21353.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3016_21353.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3016_21353.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3016_21353.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3016_21353.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3016_21353.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3016_21353.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3016_21353.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3016_21353.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3016_21353.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3016_21353.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3016_21353.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3016_21353.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3016_21353.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3016_21353.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3016_21353.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3016_21353.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21345 with
                       | (uu____21358,ty,uu____21360) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21369 =
                                 let uu____21370 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21370.FStar_Syntax_Syntax.n  in
                               match uu____21369 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21373 ->
                                   let uu____21380 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21380
                               | uu____21381 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21384 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21384
                             then
                               let uu____21389 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21391 =
                                 let uu____21393 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21393
                                  in
                               let uu____21394 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21389 uu____21391 uu____21394
                             else ());
                            r1))
                     in
                  let uu____21399 =
                    let uu____21416 = maybe_eta t1  in
                    let uu____21423 = maybe_eta t2  in
                    (uu____21416, uu____21423)  in
                  (match uu____21399 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3037_21465 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3037_21465.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3037_21465.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3037_21465.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3037_21465.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3037_21465.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3037_21465.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3037_21465.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3037_21465.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21486 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21486
                       then
                         let uu____21489 = destruct_flex_t not_abs wl  in
                         (match uu____21489 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3054_21506 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3054_21506.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3054_21506.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3054_21506.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3054_21506.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3054_21506.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3054_21506.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3054_21506.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3054_21506.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21509 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21509 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21532 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21532
                       then
                         let uu____21535 = destruct_flex_t not_abs wl  in
                         (match uu____21535 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3054_21552 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3054_21552.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3054_21552.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3054_21552.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3054_21552.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3054_21552.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3054_21552.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3054_21552.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3054_21552.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21555 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21555 orig))
                   | uu____21558 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21576,FStar_Syntax_Syntax.Tm_abs uu____21577) ->
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
                           (let uu___3016_21696 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3016_21696.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3016_21696.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3016_21696.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3016_21696.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3016_21696.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3016_21696.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3016_21696.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3016_21696.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3016_21696.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3016_21696.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3016_21696.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3016_21696.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3016_21696.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3016_21696.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3016_21696.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3016_21696.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3016_21696.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3016_21696.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3016_21696.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3016_21696.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3016_21696.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3016_21696.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3016_21696.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3016_21696.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3016_21696.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3016_21696.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3016_21696.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3016_21696.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3016_21696.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3016_21696.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3016_21696.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3016_21696.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3016_21696.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3016_21696.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3016_21696.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3016_21696.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3016_21696.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3016_21696.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3016_21696.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3016_21696.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3016_21696.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3016_21696.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3016_21696.FStar_TypeChecker_Env.erasable_types_tab)
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
                         (let uu___3037_21808 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3037_21808.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3037_21808.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3037_21808.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3037_21808.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3037_21808.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3037_21808.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3037_21808.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3037_21808.FStar_TypeChecker_Common.rank)
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
                              (let uu___3054_21849 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3054_21849.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3054_21849.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3054_21849.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3054_21849.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3054_21849.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3054_21849.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3054_21849.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3054_21849.FStar_TypeChecker_Common.rank)
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
                              (let uu___3054_21895 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3054_21895.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3054_21895.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3054_21895.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3054_21895.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3054_21895.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3054_21895.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3054_21895.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3054_21895.FStar_TypeChecker_Common.rank)
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
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21931 =
                    let uu____21936 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21936 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3077_21964 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3077_21964.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3077_21964.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3079_21966 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3079_21966.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3079_21966.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21967,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3077_21982 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3077_21982.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3077_21982.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3079_21984 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3079_21984.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3079_21984.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21985 -> (x1, x2)  in
                  (match uu____21931 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____22004 = as_refinement false env t11  in
                       (match uu____22004 with
                        | (x12,phi11) ->
                            let uu____22012 = as_refinement false env t21  in
                            (match uu____22012 with
                             | (x22,phi21) ->
                                 ((let uu____22021 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22021
                                   then
                                     ((let uu____22026 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____22028 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22030 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22026
                                         uu____22028 uu____22030);
                                      (let uu____22033 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____22035 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22037 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22033
                                         uu____22035 uu____22037))
                                   else ());
                                  (let uu____22042 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____22042 with
                                   | (base_prob,wl1) ->
                                       let x13 =
                                         FStar_Syntax_Syntax.freshen_bv x12
                                          in
                                       let subst =
                                         [FStar_Syntax_Syntax.DB
                                            (Prims.int_zero, x13)]
                                          in
                                       let phi12 =
                                         FStar_Syntax_Subst.subst subst phi11
                                          in
                                       let phi22 =
                                         FStar_Syntax_Subst.subst subst phi21
                                          in
                                       let env1 =
                                         FStar_TypeChecker_Env.push_bv env
                                           x13
                                          in
                                       let mk_imp imp phi13 phi23 =
                                         let uu____22113 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22113
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22125 =
                                         let impl =
                                           if
                                             problem.FStar_TypeChecker_Common.relation
                                               = FStar_TypeChecker_Common.EQ
                                           then
                                             mk_imp FStar_Syntax_Util.mk_iff
                                               phi12 phi22
                                           else
                                             mk_imp FStar_Syntax_Util.mk_imp
                                               phi12 phi22
                                            in
                                         let guard =
                                           FStar_Syntax_Util.mk_conj
                                             (p_guard base_prob) impl
                                            in
                                         (let uu____22138 =
                                            let uu____22141 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22141
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22138
                                            (p_guard base_prob));
                                         (let uu____22160 =
                                            let uu____22163 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22163
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22160
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22182 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22182)
                                          in
                                       let has_uvars =
                                         (let uu____22187 =
                                            let uu____22189 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22189
                                             in
                                          Prims.op_Negation uu____22187) ||
                                           (let uu____22193 =
                                              let uu____22195 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22195
                                               in
                                            Prims.op_Negation uu____22193)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22199 =
                                           let uu____22204 =
                                             let uu____22213 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22213]  in
                                           mk_t_problem wl1 uu____22204 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22199 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22236 =
                                                solve env1
                                                  (let uu___3122_22238 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3122_22238.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3122_22238.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3122_22238.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3122_22238.tcenv);
                                                     wl_implicits =
                                                       (uu___3122_22238.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3122_22238.repr_subcomp_allowed)
                                                   })
                                                 in
                                              (match uu____22236 with
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
                                               | Success uu____22253 ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22262 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22262
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3135_22271 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3135_22271.attempting);
                                                         wl_deferred =
                                                           (uu___3135_22271.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3135_22271.defer_ok);
                                                         smt_ok =
                                                           (uu___3135_22271.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3135_22271.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3135_22271.tcenv);
                                                         wl_implicits =
                                                           (uu___3135_22271.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3135_22271.repr_subcomp_allowed)
                                                       }  in
                                                     let uu____22273 =
                                                       attempt [base_prob]
                                                         wl4
                                                        in
                                                     solve env1 uu____22273))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22276,FStar_Syntax_Syntax.Tm_uvar uu____22277) ->
                  let uu____22302 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22302 with
                   | (t11,wl1) ->
                       let uu____22309 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22309 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22318;
                    FStar_Syntax_Syntax.pos = uu____22319;
                    FStar_Syntax_Syntax.vars = uu____22320;_},uu____22321),FStar_Syntax_Syntax.Tm_uvar
                 uu____22322) ->
                  let uu____22371 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22371 with
                   | (t11,wl1) ->
                       let uu____22378 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22378 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22387,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22388;
                    FStar_Syntax_Syntax.pos = uu____22389;
                    FStar_Syntax_Syntax.vars = uu____22390;_},uu____22391))
                  ->
                  let uu____22440 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22440 with
                   | (t11,wl1) ->
                       let uu____22447 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22447 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22456;
                    FStar_Syntax_Syntax.pos = uu____22457;
                    FStar_Syntax_Syntax.vars = uu____22458;_},uu____22459),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22460;
                    FStar_Syntax_Syntax.pos = uu____22461;
                    FStar_Syntax_Syntax.vars = uu____22462;_},uu____22463))
                  ->
                  let uu____22536 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22536 with
                   | (t11,wl1) ->
                       let uu____22543 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22543 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22552,uu____22553) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22566 = destruct_flex_t t1 wl  in
                  (match uu____22566 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22573;
                    FStar_Syntax_Syntax.pos = uu____22574;
                    FStar_Syntax_Syntax.vars = uu____22575;_},uu____22576),uu____22577)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22614 = destruct_flex_t t1 wl  in
                  (match uu____22614 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22621,FStar_Syntax_Syntax.Tm_uvar uu____22622) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22635,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22636;
                    FStar_Syntax_Syntax.pos = uu____22637;
                    FStar_Syntax_Syntax.vars = uu____22638;_},uu____22639))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22676,FStar_Syntax_Syntax.Tm_arrow uu____22677) ->
                  solve_t' env
                    (let uu___3237_22705 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3237_22705.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3237_22705.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3237_22705.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3237_22705.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3237_22705.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3237_22705.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3237_22705.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3237_22705.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3237_22705.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22706;
                    FStar_Syntax_Syntax.pos = uu____22707;
                    FStar_Syntax_Syntax.vars = uu____22708;_},uu____22709),FStar_Syntax_Syntax.Tm_arrow
                 uu____22710) ->
                  solve_t' env
                    (let uu___3237_22762 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3237_22762.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3237_22762.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3237_22762.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3237_22762.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3237_22762.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3237_22762.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3237_22762.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3237_22762.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3237_22762.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22763,FStar_Syntax_Syntax.Tm_uvar uu____22764) ->
                  let uu____22777 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22777
              | (uu____22778,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22779;
                    FStar_Syntax_Syntax.pos = uu____22780;
                    FStar_Syntax_Syntax.vars = uu____22781;_},uu____22782))
                  ->
                  let uu____22819 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22819
              | (FStar_Syntax_Syntax.Tm_uvar uu____22820,uu____22821) ->
                  let uu____22834 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22834
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22835;
                    FStar_Syntax_Syntax.pos = uu____22836;
                    FStar_Syntax_Syntax.vars = uu____22837;_},uu____22838),uu____22839)
                  ->
                  let uu____22876 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22876
              | (FStar_Syntax_Syntax.Tm_refine uu____22877,uu____22878) ->
                  let t21 =
                    let uu____22886 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22886  in
                  solve_t env
                    (let uu___3272_22912 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3272_22912.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3272_22912.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3272_22912.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3272_22912.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3272_22912.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3272_22912.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3272_22912.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3272_22912.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3272_22912.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22913,FStar_Syntax_Syntax.Tm_refine uu____22914) ->
                  let t11 =
                    let uu____22922 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22922  in
                  solve_t env
                    (let uu___3279_22948 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3279_22948.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3279_22948.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3279_22948.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3279_22948.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3279_22948.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3279_22948.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3279_22948.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3279_22948.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3279_22948.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____23030 =
                    let uu____23031 = guard_of_prob env wl problem t1 t2  in
                    match uu____23031 with
                    | (guard,wl1) ->
                        let uu____23038 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____23038
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23257 = br1  in
                        (match uu____23257 with
                         | (p1,w1,uu____23286) ->
                             let uu____23303 = br2  in
                             (match uu____23303 with
                              | (p2,w2,uu____23326) ->
                                  let uu____23331 =
                                    let uu____23333 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23333  in
                                  if uu____23331
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23360 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23360 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23397 = br2  in
                                         (match uu____23397 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23430 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23430
                                                 in
                                              let uu____23435 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23466,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23487) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23546 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23546 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23435
                                                (fun uu____23618  ->
                                                   match uu____23618 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23655 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23655
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23676
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23676
                                                              then
                                                                let uu____23681
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23683
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23681
                                                                  uu____23683
                                                              else ());
                                                             (let uu____23689
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23689
                                                                (fun
                                                                   uu____23725
                                                                    ->
                                                                   match uu____23725
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
                    | uu____23854 -> FStar_Pervasives_Native.None  in
                  let uu____23895 = solve_branches wl brs1 brs2  in
                  (match uu____23895 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23921 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23921 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23948 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23948 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23982 =
                                FStar_List.map
                                  (fun uu____23994  ->
                                     match uu____23994 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23982  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____24003 =
                              let uu____24004 =
                                let uu____24005 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____24005
                                  (let uu___3378_24013 = wl3  in
                                   {
                                     attempting =
                                       (uu___3378_24013.attempting);
                                     wl_deferred =
                                       (uu___3378_24013.wl_deferred);
                                     ctr = (uu___3378_24013.ctr);
                                     defer_ok = (uu___3378_24013.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3378_24013.umax_heuristic_ok);
                                     tcenv = (uu___3378_24013.tcenv);
                                     wl_implicits =
                                       (uu___3378_24013.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3378_24013.repr_subcomp_allowed)
                                   })
                                 in
                              solve env uu____24004  in
                            (match uu____24003 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____24018 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24027 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____24027 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24030,uu____24031) ->
                  let head1 =
                    let uu____24055 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24055
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24101 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24101
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24147 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24147
                    then
                      let uu____24151 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24153 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24155 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24151 uu____24153 uu____24155
                    else ());
                   (let no_free_uvars t =
                      (let uu____24169 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24169) &&
                        (let uu____24173 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24173)
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
                      let uu____24192 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24192 = FStar_Syntax_Util.Equal  in
                    let uu____24193 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24193
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24197 = equal t1 t2  in
                         (if uu____24197
                          then
                            let uu____24200 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24200
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24205 =
                            let uu____24212 = equal t1 t2  in
                            if uu____24212
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24225 = mk_eq2 wl env orig t1 t2  in
                               match uu____24225 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24205 with
                          | (guard,wl1) ->
                              let uu____24246 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24246))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24249,uu____24250) ->
                  let head1 =
                    let uu____24258 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24258
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24304 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24304
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24350 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24350
                    then
                      let uu____24354 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24356 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24358 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24354 uu____24356 uu____24358
                    else ());
                   (let no_free_uvars t =
                      (let uu____24372 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24372) &&
                        (let uu____24376 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24376)
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
                      let uu____24395 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24395 = FStar_Syntax_Util.Equal  in
                    let uu____24396 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24396
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24400 = equal t1 t2  in
                         (if uu____24400
                          then
                            let uu____24403 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24403
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24408 =
                            let uu____24415 = equal t1 t2  in
                            if uu____24415
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24428 = mk_eq2 wl env orig t1 t2  in
                               match uu____24428 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24408 with
                          | (guard,wl1) ->
                              let uu____24449 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24449))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24452,uu____24453) ->
                  let head1 =
                    let uu____24455 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24455
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24501 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24501
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24547 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24547
                    then
                      let uu____24551 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24553 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24555 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24551 uu____24553 uu____24555
                    else ());
                   (let no_free_uvars t =
                      (let uu____24569 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24569) &&
                        (let uu____24573 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24573)
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
                      let uu____24592 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24592 = FStar_Syntax_Util.Equal  in
                    let uu____24593 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24593
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24597 = equal t1 t2  in
                         (if uu____24597
                          then
                            let uu____24600 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24600
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24605 =
                            let uu____24612 = equal t1 t2  in
                            if uu____24612
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24625 = mk_eq2 wl env orig t1 t2  in
                               match uu____24625 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24605 with
                          | (guard,wl1) ->
                              let uu____24646 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24646))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24649,uu____24650) ->
                  let head1 =
                    let uu____24652 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24652
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24698 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24698
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24744 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24744
                    then
                      let uu____24748 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24750 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24752 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24748 uu____24750 uu____24752
                    else ());
                   (let no_free_uvars t =
                      (let uu____24766 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24766) &&
                        (let uu____24770 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24770)
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
                      let uu____24789 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24789 = FStar_Syntax_Util.Equal  in
                    let uu____24790 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24790
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24794 = equal t1 t2  in
                         (if uu____24794
                          then
                            let uu____24797 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24797
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24802 =
                            let uu____24809 = equal t1 t2  in
                            if uu____24809
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24822 = mk_eq2 wl env orig t1 t2  in
                               match uu____24822 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24802 with
                          | (guard,wl1) ->
                              let uu____24843 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24843))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24846,uu____24847) ->
                  let head1 =
                    let uu____24849 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24849
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24895 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24895
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24941 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24941
                    then
                      let uu____24945 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24947 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24949 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24945 uu____24947 uu____24949
                    else ());
                   (let no_free_uvars t =
                      (let uu____24963 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24963) &&
                        (let uu____24967 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24967)
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
                      let uu____24986 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24986 = FStar_Syntax_Util.Equal  in
                    let uu____24987 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24987
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24991 = equal t1 t2  in
                         (if uu____24991
                          then
                            let uu____24994 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24994
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24999 =
                            let uu____25006 = equal t1 t2  in
                            if uu____25006
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25019 = mk_eq2 wl env orig t1 t2  in
                               match uu____25019 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24999 with
                          | (guard,wl1) ->
                              let uu____25040 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25040))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25043,uu____25044) ->
                  let head1 =
                    let uu____25062 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25062
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25108 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25108
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25154 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25154
                    then
                      let uu____25158 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25160 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25162 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25158 uu____25160 uu____25162
                    else ());
                   (let no_free_uvars t =
                      (let uu____25176 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25176) &&
                        (let uu____25180 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25180)
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
                      let uu____25199 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25199 = FStar_Syntax_Util.Equal  in
                    let uu____25200 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25200
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25204 = equal t1 t2  in
                         (if uu____25204
                          then
                            let uu____25207 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25207
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25212 =
                            let uu____25219 = equal t1 t2  in
                            if uu____25219
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25232 = mk_eq2 wl env orig t1 t2  in
                               match uu____25232 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25212 with
                          | (guard,wl1) ->
                              let uu____25253 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25253))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25256,FStar_Syntax_Syntax.Tm_match uu____25257) ->
                  let head1 =
                    let uu____25281 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25281
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25327 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25327
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25373 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25373
                    then
                      let uu____25377 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25379 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25381 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25377 uu____25379 uu____25381
                    else ());
                   (let no_free_uvars t =
                      (let uu____25395 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25395) &&
                        (let uu____25399 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25399)
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
                      let uu____25418 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25418 = FStar_Syntax_Util.Equal  in
                    let uu____25419 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25419
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25423 = equal t1 t2  in
                         (if uu____25423
                          then
                            let uu____25426 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25426
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25431 =
                            let uu____25438 = equal t1 t2  in
                            if uu____25438
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25451 = mk_eq2 wl env orig t1 t2  in
                               match uu____25451 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25431 with
                          | (guard,wl1) ->
                              let uu____25472 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25472))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25475,FStar_Syntax_Syntax.Tm_uinst uu____25476) ->
                  let head1 =
                    let uu____25484 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25484
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25530 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25530
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25576 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25576
                    then
                      let uu____25580 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25582 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25584 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25580 uu____25582 uu____25584
                    else ());
                   (let no_free_uvars t =
                      (let uu____25598 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25598) &&
                        (let uu____25602 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25602)
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
                      let uu____25621 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25621 = FStar_Syntax_Util.Equal  in
                    let uu____25622 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25622
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25626 = equal t1 t2  in
                         (if uu____25626
                          then
                            let uu____25629 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25629
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25634 =
                            let uu____25641 = equal t1 t2  in
                            if uu____25641
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25654 = mk_eq2 wl env orig t1 t2  in
                               match uu____25654 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25634 with
                          | (guard,wl1) ->
                              let uu____25675 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25675))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25678,FStar_Syntax_Syntax.Tm_name uu____25679) ->
                  let head1 =
                    let uu____25681 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25681
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25727 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25727
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25767 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25767
                    then
                      let uu____25771 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25773 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25775 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25771 uu____25773 uu____25775
                    else ());
                   (let no_free_uvars t =
                      (let uu____25789 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25789) &&
                        (let uu____25793 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25793)
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
                      let uu____25812 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25812 = FStar_Syntax_Util.Equal  in
                    let uu____25813 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25813
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25817 = equal t1 t2  in
                         (if uu____25817
                          then
                            let uu____25820 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25820
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25825 =
                            let uu____25832 = equal t1 t2  in
                            if uu____25832
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25845 = mk_eq2 wl env orig t1 t2  in
                               match uu____25845 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25825 with
                          | (guard,wl1) ->
                              let uu____25866 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25866))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25869,FStar_Syntax_Syntax.Tm_constant uu____25870) ->
                  let head1 =
                    let uu____25872 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25872
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25912 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25912
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25952 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25952
                    then
                      let uu____25956 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25958 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25960 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25956 uu____25958 uu____25960
                    else ());
                   (let no_free_uvars t =
                      (let uu____25974 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25974) &&
                        (let uu____25978 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25978)
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
                      let uu____25997 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25997 = FStar_Syntax_Util.Equal  in
                    let uu____25998 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25998
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26002 = equal t1 t2  in
                         (if uu____26002
                          then
                            let uu____26005 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26005
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26010 =
                            let uu____26017 = equal t1 t2  in
                            if uu____26017
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26030 = mk_eq2 wl env orig t1 t2  in
                               match uu____26030 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26010 with
                          | (guard,wl1) ->
                              let uu____26051 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26051))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26054,FStar_Syntax_Syntax.Tm_fvar uu____26055) ->
                  let head1 =
                    let uu____26057 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26057
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26103 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26103
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26149 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26149
                    then
                      let uu____26153 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26155 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26157 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26153 uu____26155 uu____26157
                    else ());
                   (let no_free_uvars t =
                      (let uu____26171 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26171) &&
                        (let uu____26175 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26175)
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
                      let uu____26194 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26194 = FStar_Syntax_Util.Equal  in
                    let uu____26195 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26195
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26199 = equal t1 t2  in
                         (if uu____26199
                          then
                            let uu____26202 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26202
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26207 =
                            let uu____26214 = equal t1 t2  in
                            if uu____26214
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26227 = mk_eq2 wl env orig t1 t2  in
                               match uu____26227 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26207 with
                          | (guard,wl1) ->
                              let uu____26248 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26248))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26251,FStar_Syntax_Syntax.Tm_app uu____26252) ->
                  let head1 =
                    let uu____26270 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26270
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26310 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26310
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26350 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26350
                    then
                      let uu____26354 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26356 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26358 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26354 uu____26356 uu____26358
                    else ());
                   (let no_free_uvars t =
                      (let uu____26372 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26372) &&
                        (let uu____26376 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26376)
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
                      let uu____26395 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26395 = FStar_Syntax_Util.Equal  in
                    let uu____26396 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26396
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26400 = equal t1 t2  in
                         (if uu____26400
                          then
                            let uu____26403 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26403
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26408 =
                            let uu____26415 = equal t1 t2  in
                            if uu____26415
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26428 = mk_eq2 wl env orig t1 t2  in
                               match uu____26428 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26408 with
                          | (guard,wl1) ->
                              let uu____26449 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26449))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26452,FStar_Syntax_Syntax.Tm_let uu____26453) ->
                  let uu____26480 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26480
                  then
                    let uu____26483 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26483
                  else
                    (let uu____26486 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26486 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26489,uu____26490) ->
                  let uu____26504 =
                    let uu____26510 =
                      let uu____26512 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26514 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26516 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26518 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26512 uu____26514 uu____26516 uu____26518
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26510)
                     in
                  FStar_Errors.raise_error uu____26504
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26522,FStar_Syntax_Syntax.Tm_let uu____26523) ->
                  let uu____26537 =
                    let uu____26543 =
                      let uu____26545 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26547 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26549 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26551 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26545 uu____26547 uu____26549 uu____26551
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26543)
                     in
                  FStar_Errors.raise_error uu____26537
                    t1.FStar_Syntax_Syntax.pos
              | uu____26555 ->
                  let uu____26560 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26560 orig))))

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
          (let uu____26626 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26626
           then
             let uu____26631 =
               let uu____26633 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26633  in
             let uu____26634 =
               let uu____26636 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26636  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26631 uu____26634
           else ());
          (let uu____26640 =
             let uu____26642 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26642  in
           if uu____26640
           then
             let uu____26645 =
               mklstr
                 (fun uu____26652  ->
                    let uu____26653 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26655 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26653 uu____26655)
                in
             giveup env uu____26645 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26677 =
                  mklstr
                    (fun uu____26684  ->
                       let uu____26685 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26687 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26685 uu____26687)
                   in
                giveup env uu____26677 orig)
             else
               (let uu____26692 =
                  FStar_List.fold_left2
                    (fun uu____26713  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26713 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26734 =
                                 let uu____26739 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26740 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26739
                                   FStar_TypeChecker_Common.EQ uu____26740
                                   "effect universes"
                                  in
                               (match uu____26734 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26692 with
                | (univ_sub_probs,wl1) ->
                    let uu____26760 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26760 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26768 =
                           FStar_List.fold_right2
                             (fun uu____26805  ->
                                fun uu____26806  ->
                                  fun uu____26807  ->
                                    match (uu____26805, uu____26806,
                                            uu____26807)
                                    with
                                    | ((a1,uu____26851),(a2,uu____26853),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26886 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26886 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26768 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26913 =
                                  let uu____26916 =
                                    let uu____26919 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26919
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26916
                                   in
                                FStar_List.append univ_sub_probs uu____26913
                                 in
                              let guard =
                                let guard =
                                  let uu____26941 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26941  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3530_26950 = wl3  in
                                {
                                  attempting = (uu___3530_26950.attempting);
                                  wl_deferred = (uu___3530_26950.wl_deferred);
                                  ctr = (uu___3530_26950.ctr);
                                  defer_ok = (uu___3530_26950.defer_ok);
                                  smt_ok = (uu___3530_26950.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3530_26950.umax_heuristic_ok);
                                  tcenv = (uu___3530_26950.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3530_26950.repr_subcomp_allowed)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26952 = attempt sub_probs wl5  in
                              solve env uu____26952))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26970 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26970
           then
             let uu____26975 =
               let uu____26977 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26977
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26979 =
               let uu____26981 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26981
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26975 uu____26979
           else ());
          (let uu____26986 =
             let uu____26991 =
               let uu____26996 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26996
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26991
               (fun uu____27013  ->
                  match uu____27013 with
                  | (c,g) ->
                      let uu____27024 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____27024, g))
              in
           match uu____26986 with
           | (c12,g_lift) ->
               ((let uu____27028 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____27028
                 then
                   let uu____27033 =
                     let uu____27035 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27035
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____27037 =
                     let uu____27039 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27039
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____27033 uu____27037
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3550_27049 = wl  in
                     {
                       attempting = (uu___3550_27049.attempting);
                       wl_deferred = (uu___3550_27049.wl_deferred);
                       ctr = (uu___3550_27049.ctr);
                       defer_ok = (uu___3550_27049.defer_ok);
                       smt_ok = (uu___3550_27049.smt_ok);
                       umax_heuristic_ok =
                         (uu___3550_27049.umax_heuristic_ok);
                       tcenv = (uu___3550_27049.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits);
                       repr_subcomp_allowed =
                         (uu___3550_27049.repr_subcomp_allowed)
                     }  in
                   let uu____27050 =
                     let rec is_uvar t =
                       let uu____27064 =
                         let uu____27065 = FStar_Syntax_Subst.compress t  in
                         uu____27065.FStar_Syntax_Syntax.n  in
                       match uu____27064 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____27069 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27084) ->
                           is_uvar t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27090) ->
                           is_uvar t1
                       | uu____27115 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27149  ->
                          fun uu____27150  ->
                            fun uu____27151  ->
                              match (uu____27149, uu____27150, uu____27151)
                              with
                              | ((a1,uu____27195),(a2,uu____27197),(is_sub_probs,wl2))
                                  ->
                                  let uu____27230 = is_uvar a1  in
                                  if uu____27230
                                  then
                                    ((let uu____27240 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27240
                                      then
                                        let uu____27245 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27247 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27245 uu____27247
                                      else ());
                                     (let uu____27252 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27252 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____27050 with
                   | (is_sub_probs,wl2) ->
                       let uu____27280 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27280 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27288 =
                              let uu____27293 =
                                let uu____27294 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27294
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27293
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27288 with
                             | (uu____27301,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27312 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27314 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27312 s uu____27314
                                    in
                                 let uu____27317 =
                                   let uu____27346 =
                                     let uu____27347 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27347.FStar_Syntax_Syntax.n  in
                                   match uu____27346 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27407 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27407 with
                                        | (bs',c3) ->
                                            let a = FStar_List.hd bs'  in
                                            let bs1 = FStar_List.tail bs'  in
                                            let uu____27470 =
                                              let uu____27489 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27489
                                                (fun uu____27593  ->
                                                   match uu____27593 with
                                                   | (l1,l2) ->
                                                       let uu____27666 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27666))
                                               in
                                            (match uu____27470 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27771 ->
                                       let uu____27772 =
                                         let uu____27778 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27778)
                                          in
                                       FStar_Errors.raise_error uu____27772 r
                                    in
                                 (match uu____27317 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27854 =
                                        let uu____27861 =
                                          let uu____27862 =
                                            let uu____27863 =
                                              let uu____27870 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27870,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27863
                                             in
                                          [uu____27862]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27861
                                          (fun b  ->
                                             let uu____27886 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27888 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27890 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27886 uu____27888
                                               uu____27890) r
                                         in
                                      (match uu____27854 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27900 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27900
                                             then
                                               let uu____27905 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27914 =
                                                          let uu____27916 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27916
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27914) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27905
                                             else ());
                                            (let wl4 =
                                               let uu___3622_27924 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3622_27924.attempting);
                                                 wl_deferred =
                                                   (uu___3622_27924.wl_deferred);
                                                 ctr = (uu___3622_27924.ctr);
                                                 defer_ok =
                                                   (uu___3622_27924.defer_ok);
                                                 smt_ok =
                                                   (uu___3622_27924.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3622_27924.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3622_27924.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits);
                                                 repr_subcomp_allowed =
                                                   (uu___3622_27924.repr_subcomp_allowed)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27949 =
                                                        let uu____27956 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27956, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27949) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27973 =
                                               let f_sort_is =
                                                 let uu____27983 =
                                                   let uu____27984 =
                                                     let uu____27987 =
                                                       let uu____27988 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27988.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27987
                                                      in
                                                   uu____27984.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27983 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27999,uu____28000::is)
                                                     ->
                                                     let uu____28042 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____28042
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28075 ->
                                                     let uu____28076 =
                                                       let uu____28082 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28082)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28076 r
                                                  in
                                               let uu____28088 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28123  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28123
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28144 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28144
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28088
                                                in
                                             match uu____27973 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28169 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28169
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28170 =
                                                   let g_sort_is =
                                                     let uu____28180 =
                                                       let uu____28181 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28181.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28180 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28186,uu____28187::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28247 ->
                                                         let uu____28248 =
                                                           let uu____28254 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28254)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28248 r
                                                      in
                                                   let uu____28260 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28295  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28295
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28316
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28316
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28260
                                                    in
                                                 (match uu____28170 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28343 =
                                                          let uu____28348 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28349 =
                                                            let uu____28350 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28350
                                                             in
                                                          (uu____28348,
                                                            uu____28349)
                                                           in
                                                        match uu____28343
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28378 =
                                                          let uu____28381 =
                                                            let uu____28384 =
                                                              let uu____28387
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28387
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28384
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28381
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28378
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28411 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28411
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
                                                        let uu____28422 =
                                                          let uu____28425 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun uu____28428 
                                                               ->
                                                               FStar_Pervasives_Native.Some
                                                                 uu____28428)
                                                            uu____28425
                                                           in
                                                        solve_prob orig
                                                          uu____28422 [] wl6
                                                         in
                                                      let uu____28429 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28429))))))))))
           in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env  in
           let lift_c1 uu____28457 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____28459 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ
                      in
                   [uu____28459]
               | x -> x  in
             let c12 =
               let uu___3690_28462 = c11  in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3690_28462.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3690_28462.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3690_28462.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3690_28462.FStar_Syntax_Syntax.flags)
               }  in
             let uu____28463 =
               let uu____28468 =
                 FStar_All.pipe_right
                   (let uu___3693_28470 = c12  in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3693_28470.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3693_28470.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3693_28470.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3693_28470.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____28468
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____28463
               (fun uu____28484  ->
                  match uu____28484 with
                  | (c,g) ->
                      let uu____28491 =
                        let uu____28493 = FStar_TypeChecker_Env.is_trivial g
                           in
                        Prims.op_Negation uu____28493  in
                      if uu____28491
                      then
                        let uu____28496 =
                          let uu____28502 =
                            let uu____28504 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name
                               in
                            let uu____28506 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name
                               in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____28504 uu____28506
                             in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____28502)
                           in
                        FStar_Errors.raise_error uu____28496 r
                      else FStar_Syntax_Util.comp_to_comp_typ c)
              in
           let uu____28512 =
             FStar_TypeChecker_Env.is_layered_effect env
               c21.FStar_Syntax_Syntax.effect_name
              in
           if uu____28512
           then solve_layered_sub c11 edge c21
           else
             (let uu____28517 =
                ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                   (let uu____28520 =
                      FStar_Ident.lid_equals
                        c11.FStar_Syntax_Syntax.effect_name
                        c21.FStar_Syntax_Syntax.effect_name
                       in
                    Prims.op_Negation uu____28520))
                  &&
                  (FStar_TypeChecker_Env.is_reifiable_effect env
                     c21.FStar_Syntax_Syntax.effect_name)
                 in
              if uu____28517
              then
                let uu____28523 =
                  mklstr
                    (fun uu____28530  ->
                       let uu____28531 =
                         FStar_Ident.string_of_lid
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____28533 =
                         FStar_Ident.string_of_lid
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Cannot lift from %s to %s, it needs a lift\n"
                         uu____28531 uu____28533)
                   in
                giveup env uu____28523 orig
              else
                (let is_null_wp_2 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___28_28544  ->
                           match uu___28_28544 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | FStar_Syntax_Syntax.MLEFFECT  -> true
                           | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                           | uu____28549 -> false))
                    in
                 let uu____28551 =
                   match ((c11.FStar_Syntax_Syntax.effect_args),
                           (c21.FStar_Syntax_Syntax.effect_args))
                   with
                   | ((wp1,uu____28581)::uu____28582,(wp2,uu____28584)::uu____28585)
                       -> (wp1, wp2)
                   | uu____28658 ->
                       let uu____28683 =
                         let uu____28689 =
                           let uu____28691 =
                             FStar_Syntax_Print.lid_to_string
                               c11.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28693 =
                             FStar_Syntax_Print.lid_to_string
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Got effects %s and %s, expected normalized effects"
                             uu____28691 uu____28693
                            in
                         (FStar_Errors.Fatal_ExpectNormalizedEffect,
                           uu____28689)
                          in
                       FStar_Errors.raise_error uu____28683
                         env.FStar_TypeChecker_Env.range
                    in
                 match uu____28551 with
                 | (wpc1,wpc2) ->
                     let uu____28703 = FStar_Util.physical_equality wpc1 wpc2
                        in
                     if uu____28703
                     then
                       let uu____28706 =
                         problem_using_guard orig
                           c11.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____28706 wl
                     else
                       (let uu____28710 =
                          let uu____28717 =
                            FStar_TypeChecker_Env.effect_decl_opt env
                              c21.FStar_Syntax_Syntax.effect_name
                             in
                          FStar_Util.must uu____28717  in
                        match uu____28710 with
                        | (c2_decl,qualifiers) ->
                            let uu____28738 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            if uu____28738
                            then
                              let c1_repr =
                                let uu____28745 =
                                  let uu____28746 =
                                    let uu____28747 = lift_c1 ()  in
                                    FStar_Syntax_Syntax.mk_Comp uu____28747
                                     in
                                  let uu____28748 =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  FStar_TypeChecker_Env.reify_comp env
                                    uu____28746 uu____28748
                                   in
                                norm_with_steps
                                  "FStar.TypeChecker.Rel.norm_with_steps.4"
                                  [FStar_TypeChecker_Env.UnfoldUntil
                                     FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Env.Weak;
                                  FStar_TypeChecker_Env.HNF] env uu____28745
                                 in
                              let c2_repr =
                                let uu____28751 =
                                  let uu____28752 =
                                    FStar_Syntax_Syntax.mk_Comp c21  in
                                  let uu____28753 =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  FStar_TypeChecker_Env.reify_comp env
                                    uu____28752 uu____28753
                                   in
                                norm_with_steps
                                  "FStar.TypeChecker.Rel.norm_with_steps.5"
                                  [FStar_TypeChecker_Env.UnfoldUntil
                                     FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Env.Weak;
                                  FStar_TypeChecker_Env.HNF] env uu____28751
                                 in
                              let uu____28755 =
                                let uu____28760 =
                                  let uu____28762 =
                                    FStar_Syntax_Print.term_to_string c1_repr
                                     in
                                  let uu____28764 =
                                    FStar_Syntax_Print.term_to_string c2_repr
                                     in
                                  FStar_Util.format2
                                    "sub effect repr: %s <: %s" uu____28762
                                    uu____28764
                                   in
                                sub_prob wl c1_repr
                                  problem.FStar_TypeChecker_Common.relation
                                  c2_repr uu____28760
                                 in
                              (match uu____28755 with
                               | (prob,wl1) ->
                                   let wl2 =
                                     solve_prob orig
                                       (FStar_Pervasives_Native.Some
                                          (p_guard prob)) [] wl1
                                      in
                                   let uu____28770 = attempt [prob] wl2  in
                                   solve env uu____28770)
                            else
                              (let g =
                                 if env.FStar_TypeChecker_Env.lax
                                 then FStar_Syntax_Util.t_true
                                 else
                                   (let wpc1_2 =
                                      let uu____28790 = lift_c1 ()  in
                                      FStar_All.pipe_right uu____28790
                                        (fun ct  ->
                                           FStar_List.hd
                                             ct.FStar_Syntax_Syntax.effect_args)
                                       in
                                    if is_null_wp_2
                                    then
                                      ((let uu____28813 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other "Rel")
                                           in
                                        if uu____28813
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
                                          let uu____28823 =
                                            FStar_All.pipe_right c2_decl
                                              FStar_Syntax_Util.get_wp_trivial_combinator
                                             in
                                          match uu____28823 with
                                          | FStar_Pervasives_Native.None  ->
                                              failwith
                                                "Rel doesn't yet handle undefined trivial combinator in an effect"
                                          | FStar_Pervasives_Native.Some t ->
                                              t
                                           in
                                        let uu____28830 =
                                          let uu____28837 =
                                            let uu____28838 =
                                              let uu____28855 =
                                                FStar_TypeChecker_Env.inst_effect_fun_with
                                                  [c1_univ] env c2_decl
                                                  trivial
                                                 in
                                              let uu____28858 =
                                                let uu____28869 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                   in
                                                [uu____28869; wpc1_2]  in
                                              (uu____28855, uu____28858)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____28838
                                             in
                                          FStar_Syntax_Syntax.mk uu____28837
                                           in
                                        uu____28830
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
                                       let uu____28918 =
                                         let uu____28925 =
                                           let uu____28926 =
                                             let uu____28943 =
                                               FStar_TypeChecker_Env.inst_effect_fun_with
                                                 [c2_univ] env c2_decl
                                                 stronger
                                                in
                                             let uu____28946 =
                                               let uu____28957 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   c21.FStar_Syntax_Syntax.result_typ
                                                  in
                                               let uu____28966 =
                                                 let uu____28977 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     wpc2
                                                    in
                                                 [uu____28977; wpc1_2]  in
                                               uu____28957 :: uu____28966  in
                                             (uu____28943, uu____28946)  in
                                           FStar_Syntax_Syntax.Tm_app
                                             uu____28926
                                            in
                                         FStar_Syntax_Syntax.mk uu____28925
                                          in
                                       uu____28918
                                         FStar_Pervasives_Native.None r))
                                  in
                               (let uu____29031 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____29031
                                then
                                  let uu____29036 =
                                    let uu____29038 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Iota;
                                        FStar_TypeChecker_Env.Eager_unfolding;
                                        FStar_TypeChecker_Env.Primops;
                                        FStar_TypeChecker_Env.Simplify] env g
                                       in
                                    FStar_Syntax_Print.term_to_string
                                      uu____29038
                                     in
                                  FStar_Util.print1
                                    "WP guard (simplifed) is (%s)\n"
                                    uu____29036
                                else ());
                               (let uu____29042 =
                                  sub_prob wl
                                    c11.FStar_Syntax_Syntax.result_typ
                                    problem.FStar_TypeChecker_Common.relation
                                    c21.FStar_Syntax_Syntax.result_typ
                                    "result type"
                                   in
                                match uu____29042 with
                                | (base_prob,wl1) ->
                                    let wl2 =
                                      let uu____29051 =
                                        let uu____29054 =
                                          FStar_Syntax_Util.mk_conj
                                            (p_guard base_prob) g
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____29057  ->
                                             FStar_Pervasives_Native.Some
                                               uu____29057) uu____29054
                                         in
                                      solve_prob orig uu____29051 [] wl1  in
                                    let uu____29058 = attempt [base_prob] wl2
                                       in
                                    solve env uu____29058))))))
           in
        let uu____29059 = FStar_Util.physical_equality c1 c2  in
        if uu____29059
        then
          let uu____29062 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____29062
        else
          ((let uu____29066 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____29066
            then
              let uu____29071 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____29073 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29071
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29073
            else ());
           (let uu____29078 =
              let uu____29087 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29090 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29087, uu____29090)  in
            match uu____29078 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29108),FStar_Syntax_Syntax.Total
                    (t2,uu____29110)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29127 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29127 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29129,FStar_Syntax_Syntax.Total uu____29130) ->
                     let uu____29147 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29147 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29151),FStar_Syntax_Syntax.Total
                    (t2,uu____29153)) ->
                     let uu____29170 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29170 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29173),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29175)) ->
                     let uu____29192 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29192 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29195),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29197)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29214 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29214 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29217),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29219)) ->
                     let uu____29236 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29236 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29239,FStar_Syntax_Syntax.Comp uu____29240) ->
                     let uu____29249 =
                       let uu___3818_29252 = problem  in
                       let uu____29255 =
                         let uu____29256 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29256
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3818_29252.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29255;
                         FStar_TypeChecker_Common.relation =
                           (uu___3818_29252.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3818_29252.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3818_29252.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3818_29252.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3818_29252.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3818_29252.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3818_29252.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3818_29252.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29249 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29257,FStar_Syntax_Syntax.Comp uu____29258) ->
                     let uu____29267 =
                       let uu___3818_29270 = problem  in
                       let uu____29273 =
                         let uu____29274 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29274
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3818_29270.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29273;
                         FStar_TypeChecker_Common.relation =
                           (uu___3818_29270.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3818_29270.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3818_29270.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3818_29270.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3818_29270.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3818_29270.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3818_29270.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3818_29270.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29267 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29275,FStar_Syntax_Syntax.GTotal uu____29276) ->
                     let uu____29285 =
                       let uu___3830_29288 = problem  in
                       let uu____29291 =
                         let uu____29292 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29292
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3830_29288.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3830_29288.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3830_29288.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29291;
                         FStar_TypeChecker_Common.element =
                           (uu___3830_29288.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3830_29288.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3830_29288.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3830_29288.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3830_29288.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3830_29288.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29285 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29293,FStar_Syntax_Syntax.Total uu____29294) ->
                     let uu____29303 =
                       let uu___3830_29306 = problem  in
                       let uu____29309 =
                         let uu____29310 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29310
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3830_29306.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3830_29306.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3830_29306.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29309;
                         FStar_TypeChecker_Common.element =
                           (uu___3830_29306.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3830_29306.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3830_29306.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3830_29306.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3830_29306.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3830_29306.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29303 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29311,FStar_Syntax_Syntax.Comp uu____29312) ->
                     let uu____29313 =
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
                     if uu____29313
                     then
                       let uu____29316 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29316 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29323 =
                            let uu____29328 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29328
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29337 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29338 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29337, uu____29338))
                             in
                          match uu____29323 with
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
                           (let uu____29346 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29346
                            then
                              let uu____29351 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name
                                 in
                              let uu____29353 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____29351 uu____29353
                            else ());
                           (let uu____29358 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29358 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29361 =
                                  mklstr
                                    (fun uu____29368  ->
                                       let uu____29369 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29371 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29369 uu____29371)
                                   in
                                giveup env uu____29361 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29382 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29382 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29432 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29432 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29457 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29488  ->
                match uu____29488 with
                | (u1,u2) ->
                    let uu____29496 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29498 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29496 uu____29498))
         in
      FStar_All.pipe_right uu____29457 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29535,[])) when
          let uu____29562 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29562 -> "{}"
      | uu____29565 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29592 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29592
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29604 =
              FStar_List.map
                (fun uu____29617  ->
                   match uu____29617 with
                   | (uu____29624,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29604 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29635 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29635 imps
  
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
                  let uu____29692 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29692
                  then
                    let uu____29700 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29702 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29700
                      (rel_to_string rel) uu____29702
                  else "TOP"  in
                let uu____29708 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29708 with
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
              let uu____29768 =
                let uu____29771 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun uu____29774  ->
                     FStar_Pervasives_Native.Some uu____29774) uu____29771
                 in
              FStar_Syntax_Syntax.new_bv uu____29768 t1  in
            let uu____29775 =
              let uu____29780 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29780
               in
            match uu____29775 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29838 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29838
         then
           let uu____29843 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29843
         else ());
        (let uu____29850 =
           FStar_Util.record_time (fun uu____29857  -> solve env probs)  in
         match uu____29850 with
         | (sol,ms) ->
             ((let uu____29869 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29869
               then
                 let uu____29874 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29874
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29887 =
                     FStar_Util.record_time
                       (fun uu____29894  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29887 with
                    | ((),ms1) ->
                        ((let uu____29905 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29905
                          then
                            let uu____29910 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29910
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29922 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29922
                     then
                       let uu____29929 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29929
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
          ((let uu____29955 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29955
            then
              let uu____29960 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29960
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29968 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29968
             then
               let uu____29973 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29973
             else ());
            (let f2 =
               let uu____29979 =
                 let uu____29980 = FStar_Syntax_Util.unmeta f1  in
                 uu____29980.FStar_Syntax_Syntax.n  in
               match uu____29979 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29984 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3947_29985 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3947_29985.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3947_29985.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3947_29985.FStar_TypeChecker_Common.implicits)
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
            let uu____30028 =
              let uu____30029 =
                let uu____30030 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____30031  ->
                       FStar_TypeChecker_Common.NonTrivial uu____30031)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30030;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____30029  in
            FStar_All.pipe_left
              (fun uu____30038  -> FStar_Pervasives_Native.Some uu____30038)
              uu____30028
  
let with_guard_no_simp :
  'uuuuuu30048 .
    'uuuuuu30048 ->
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
            let uu____30088 =
              let uu____30089 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____30090  ->
                     FStar_TypeChecker_Common.NonTrivial uu____30090)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30089;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30088
  
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
          (let uu____30123 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30123
           then
             let uu____30128 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30130 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30128
               uu____30130
           else ());
          (let uu____30135 =
             let uu____30140 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30140
              in
           match uu____30135 with
           | (prob,wl) ->
               let g =
                 let uu____30148 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30156  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30148  in
               ((let uu____30174 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30174
                 then
                   let uu____30179 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30179
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
        let uu____30200 = try_teq true env t1 t2  in
        match uu____30200 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30205 = FStar_TypeChecker_Env.get_range env  in
              let uu____30206 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30205 uu____30206);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30214 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30214
              then
                let uu____30219 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30221 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30223 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30219
                  uu____30221 uu____30223
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
        (let uu____30247 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30247
         then
           let uu____30252 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30254 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30252
             uu____30254
         else ());
        (let uu____30259 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30259 with
         | (prob,x,wl) ->
             let g =
               let uu____30274 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30283  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30274  in
             ((let uu____30301 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30301
               then
                 let uu____30306 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30306
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30314 =
                     let uu____30315 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30315 g1  in
                   FStar_Pervasives_Native.Some uu____30314)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30337 = FStar_TypeChecker_Env.get_range env  in
          let uu____30338 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30337 uu____30338
  
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
        (let uu____30367 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30367
         then
           let uu____30372 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30374 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30372 uu____30374
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30385 =
           let uu____30392 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30392 "sub_comp"
            in
         match uu____30385 with
         | (prob,wl) ->
             let wl1 =
               let uu___4018_30403 = wl  in
               {
                 attempting = (uu___4018_30403.attempting);
                 wl_deferred = (uu___4018_30403.wl_deferred);
                 ctr = (uu___4018_30403.ctr);
                 defer_ok = (uu___4018_30403.defer_ok);
                 smt_ok = (uu___4018_30403.smt_ok);
                 umax_heuristic_ok = (uu___4018_30403.umax_heuristic_ok);
                 tcenv = (uu___4018_30403.tcenv);
                 wl_implicits = (uu___4018_30403.wl_implicits);
                 repr_subcomp_allowed = true
               }  in
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30408 =
                 FStar_Util.record_time
                   (fun uu____30420  ->
                      let uu____30421 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____30430  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30421)
                  in
               match uu____30408 with
               | (r,ms) ->
                   ((let uu____30458 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30458
                     then
                       let uu____30463 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30465 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30467 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30463 uu____30465
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30467
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
      fun uu____30505  ->
        match uu____30505 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30548 =
                 let uu____30554 =
                   let uu____30556 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30558 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30556 uu____30558
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30554)  in
               let uu____30562 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30548 uu____30562)
               in
            let equiv v v' =
              let uu____30575 =
                let uu____30580 = FStar_Syntax_Subst.compress_univ v  in
                let uu____30581 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30580, uu____30581)  in
              match uu____30575 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30605 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v  ->
                      let uu____30636 = FStar_Syntax_Subst.compress_univ v
                         in
                      match uu____30636 with
                      | FStar_Syntax_Syntax.U_unif uu____30643 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30674  ->
                                    match uu____30674 with
                                    | (u,v') ->
                                        let uu____30683 = equiv v v'  in
                                        if uu____30683
                                        then
                                          let uu____30688 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____30688 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v)]
                      | uu____30709 -> []))
               in
            let uu____30714 =
              let wl =
                let uu___4061_30718 = empty_worklist env  in
                {
                  attempting = (uu___4061_30718.attempting);
                  wl_deferred = (uu___4061_30718.wl_deferred);
                  ctr = (uu___4061_30718.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4061_30718.smt_ok);
                  umax_heuristic_ok = (uu___4061_30718.umax_heuristic_ok);
                  tcenv = (uu___4061_30718.tcenv);
                  wl_implicits = (uu___4061_30718.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4061_30718.repr_subcomp_allowed)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30737  ->
                      match uu____30737 with
                      | (lb,v) ->
                          let uu____30744 =
                            solve_universe_eq (~- Prims.int_one) wl lb v  in
                          (match uu____30744 with
                           | USolved wl1 -> ()
                           | uu____30747 -> fail lb v)))
               in
            let rec check_ineq uu____30758 =
              match uu____30758 with
              | (u,v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v  in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30770) -> true
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
                      uu____30798,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30800,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30813) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v1)))
                   | (uu____30821,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v2  -> check_ineq (u1, v2)))
                   | uu____30830 -> false)
               in
            let uu____30836 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30853  ->
                      match uu____30853 with
                      | (u,v) ->
                          let uu____30861 = check_ineq (u, v)  in
                          if uu____30861
                          then true
                          else
                            ((let uu____30869 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30869
                              then
                                let uu____30874 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30876 =
                                  FStar_Syntax_Print.univ_to_string v  in
                                FStar_Util.print2 "%s </= %s" uu____30874
                                  uu____30876
                              else ());
                             false)))
               in
            if uu____30836
            then ()
            else
              ((let uu____30886 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30886
                then
                  ((let uu____30892 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30892);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30904 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30904))
                else ());
               (let uu____30917 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30917))
  
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
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun defer_ok  ->
    fun smt_ok  ->
      fun env  ->
        fun g  ->
          let fail uu____30997 =
            match uu____30997 with
            | (d,s) ->
                let msg = explain env d s  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d)
             in
          let wl =
            let uu___4139_31020 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
            {
              attempting = (uu___4139_31020.attempting);
              wl_deferred = (uu___4139_31020.wl_deferred);
              ctr = (uu___4139_31020.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4139_31020.umax_heuristic_ok);
              tcenv = (uu___4139_31020.tcenv);
              wl_implicits = (uu___4139_31020.wl_implicits);
              repr_subcomp_allowed = (uu___4139_31020.repr_subcomp_allowed)
            }  in
          (let uu____31023 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____31023
           then
             let uu____31028 = FStar_Util.string_of_bool defer_ok  in
             let uu____31030 = wl_to_string wl  in
             let uu____31032 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits)
                in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____31028 uu____31030 uu____31032
           else ());
          (let g1 =
             let uu____31038 = solve_and_commit env wl fail  in
             match uu____31038 with
             | FStar_Pervasives_Native.Some
                 (uu____31045::uu____31046,uu____31047) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred,imps) ->
                 let uu___4154_31076 = g  in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4154_31076.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4154_31076.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____31077 ->
                 failwith "Impossible: should have raised a failure already"
              in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let uu___4159_31086 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4159_31086.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred =
                (uu___4159_31086.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs = ([], []);
              FStar_TypeChecker_Common.implicits =
                (uu___4159_31086.FStar_TypeChecker_Common.implicits)
            }))
  
let (solve_deferred_constraints' :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun smt_ok  ->
    fun env  -> fun g  -> try_solve_deferred_constraints false smt_ok env g
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> solve_deferred_constraints' true env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true true env g 
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
          let debug =
            ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel"))
               ||
               (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "SMTQuery")))
              ||
              (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Tac"))
             in
          let g1 = solve_deferred_constraints' use_smt env g  in
          let ret_g =
            let uu___4174_31183 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4174_31183.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4174_31183.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4174_31183.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____31184 =
            let uu____31186 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____31186  in
          if uu____31184
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug
                  then
                    (let uu____31198 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____31199 =
                       let uu____31201 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____31201
                        in
                     FStar_Errors.diag uu____31198 uu____31199)
                  else ();
                  (let vc1 =
                     let uu____31207 =
                       let uu____31211 =
                         let uu____31213 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____31213  in
                       FStar_Pervasives_Native.Some uu____31211  in
                     FStar_Profiling.profile
                       (fun uu____31216  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____31207 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug
                   then
                     (let uu____31220 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31221 =
                        let uu____31223 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31223
                         in
                      FStar_Errors.diag uu____31220 uu____31221)
                   else ();
                   (let uu____31229 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31229
                      "discharge_guard'" env vc1);
                   (let uu____31231 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31231 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug
                           then
                             (let uu____31240 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31241 =
                                let uu____31243 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31243
                                 in
                              FStar_Errors.diag uu____31240 uu____31241)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug
                           then
                             (let uu____31253 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31254 =
                                let uu____31256 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31256
                                 in
                              FStar_Errors.diag uu____31253 uu____31254)
                           else ();
                           (let vcs =
                              let uu____31270 = FStar_Options.use_tactics ()
                                 in
                              if uu____31270
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31292  ->
                                     (let uu____31294 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        (fun uu____31296  -> ()) uu____31294);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31339  ->
                                              match uu____31339 with
                                              | (env1,goal,opts) ->
                                                  let uu____31355 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31355, opts)))))
                              else
                                (let uu____31359 =
                                   let uu____31366 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31366)  in
                                 [uu____31359])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31399  ->
                                    match uu____31399 with
                                    | (env1,goal,opts) ->
                                        let uu____31409 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31409 with
                                         | FStar_TypeChecker_Common.Trivial 
                                             ->
                                             if debug
                                             then
                                               FStar_Util.print_string
                                                 "Goal completely solved by tactic\n"
                                             else ()
                                         | FStar_TypeChecker_Common.NonTrivial
                                             goal1 ->
                                             (FStar_Options.push ();
                                              FStar_Options.set opts;
                                              if debug
                                              then
                                                (let uu____31420 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31421 =
                                                   let uu____31423 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31425 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31423 uu____31425
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31420 uu____31421)
                                              else ();
                                              if debug
                                              then
                                                (let uu____31432 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31433 =
                                                   let uu____31435 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31435
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31432 uu____31433)
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
      let uu____31453 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31453 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31462 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31462
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31476 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31476 with
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
        let uu____31506 = try_teq false env t1 t2  in
        match uu____31506 with
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
            let uu____31550 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31550 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31563 ->
                     let uu____31576 =
                       let uu____31577 = FStar_Syntax_Subst.compress r  in
                       uu____31577.FStar_Syntax_Syntax.n  in
                     (match uu____31576 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31582) ->
                          unresolved ctx_u'
                      | uu____31599 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31623 = acc  in
            match uu____31623 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd::tl ->
                     let uu____31642 = hd  in
                     (match uu____31642 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl
                          else
                            (let uu____31653 = unresolved ctx_u  in
                             if uu____31653
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd :: out), changed) tl
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31677 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31677
                                     then
                                       let uu____31681 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31681
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31690 = teq_nosmt env1 t tm
                                          in
                                       match uu____31690 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4287_31700 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4287_31700.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4287_31700.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4287_31700.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4287_31700.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4287_31700.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4287_31700.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4287_31700.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd1 =
                                       let uu___4290_31708 = hd  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4290_31708.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4290_31708.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4290_31708.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl)))
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl
                               else
                                 (let env1 =
                                    let uu___4294_31719 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4294_31719.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4294_31719.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4294_31719.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4294_31719.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4294_31719.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4294_31719.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4294_31719.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4294_31719.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4294_31719.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4294_31719.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4294_31719.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4294_31719.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4294_31719.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4294_31719.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4294_31719.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4294_31719.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4294_31719.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4294_31719.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4294_31719.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4294_31719.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4294_31719.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4294_31719.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4294_31719.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4294_31719.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4294_31719.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4294_31719.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4294_31719.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4294_31719.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4294_31719.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4294_31719.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4294_31719.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4294_31719.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4294_31719.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4294_31719.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4294_31719.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4294_31719.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4294_31719.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4294_31719.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4294_31719.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4294_31719.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4294_31719.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4294_31719.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4294_31719.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4294_31719.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4294_31719.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4299_31724 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4299_31724.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4299_31724.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4299_31724.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4299_31724.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4299_31724.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4299_31724.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4299_31724.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4299_31724.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4299_31724.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4299_31724.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4299_31724.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4299_31724.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4299_31724.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4299_31724.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4299_31724.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4299_31724.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4299_31724.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4299_31724.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4299_31724.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4299_31724.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4299_31724.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4299_31724.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4299_31724.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4299_31724.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4299_31724.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4299_31724.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4299_31724.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4299_31724.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4299_31724.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4299_31724.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4299_31724.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4299_31724.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4299_31724.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4299_31724.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4299_31724.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4299_31724.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4299_31724.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4299_31724.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4299_31724.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4299_31724.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4299_31724.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4299_31724.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4299_31724.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4299_31724.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4299_31724.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31729 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31729
                                   then
                                     let uu____31734 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31736 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31738 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31740 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31734 uu____31736 uu____31738
                                       reason uu____31740
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4305_31747  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31754 =
                                             let uu____31764 =
                                               let uu____31772 =
                                                 let uu____31774 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31776 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31778 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31774 uu____31776
                                                   uu____31778
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31772, r)
                                                in
                                             [uu____31764]  in
                                           FStar_Errors.add_errors
                                             uu____31754);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31797 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31808  ->
                                               let uu____31809 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31811 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31813 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31809 uu____31811
                                                 reason uu____31813)) env2 g1
                                         true
                                        in
                                     match uu____31797 with
                                     | FStar_Pervasives_Native.Some g2 -> g2
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Common.implicits
                                         out), true) tl)))))
             in
          let uu___4317_31821 = g  in
          let uu____31822 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4317_31821.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4317_31821.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4317_31821.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31822
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
        let uu____31862 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31862 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31863 = discharge_guard env g1  in
          FStar_All.pipe_left (fun uu____31864  -> ()) uu____31863
      | imp::uu____31866 ->
          let uu____31869 =
            let uu____31875 =
              let uu____31877 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31879 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31877 uu____31879
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31875)
             in
          FStar_Errors.raise_error uu____31869
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31899 = teq env t1 t2  in
        force_trivial_guard env uu____31899
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31918 = teq_nosmt env t1 t2  in
        match uu____31918 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4342_31937 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4342_31937.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4342_31937.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4342_31937.FStar_TypeChecker_Common.implicits)
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
        (let uu____31973 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31973
         then
           let uu____31978 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31980 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31978
             uu____31980
         else ());
        (let uu____31985 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31985 with
         | (prob,x,wl) ->
             let g =
               let uu____32004 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____32013  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32004  in
             ((let uu____32031 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____32031
               then
                 let uu____32036 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____32038 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____32040 =
                   let uu____32042 = FStar_Util.must g  in
                   guard_to_string env uu____32042  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____32036 uu____32038 uu____32040
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
        let uu____32079 = check_subtyping env t1 t2  in
        match uu____32079 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32098 =
              let uu____32099 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____32099 g  in
            FStar_Pervasives_Native.Some uu____32098
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32118 = check_subtyping env t1 t2  in
        match uu____32118 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32137 =
              let uu____32138 =
                let uu____32139 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____32139]  in
              FStar_TypeChecker_Env.close_guard env uu____32138 g  in
            FStar_Pervasives_Native.Some uu____32137
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32177 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32177
         then
           let uu____32182 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32184 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32182
             uu____32184
         else ());
        (let uu____32189 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32189 with
         | (prob,x,wl) ->
             let g =
               let uu____32204 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32213  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32204  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32234 =
                      let uu____32235 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32235]  in
                    FStar_TypeChecker_Env.close_guard env uu____32234 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32276 = subtype_nosmt env t1 t2  in
        match uu____32276 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  