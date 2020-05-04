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
                     ((let uu___81_668 = wl  in
                       {
                         attempting = (uu___81_668.attempting);
                         wl_deferred = (uu___81_668.wl_deferred);
                         ctr = (uu___81_668.ctr);
                         defer_ok = (uu___81_668.defer_ok);
                         smt_ok = (uu___81_668.smt_ok);
                         umax_heuristic_ok = (uu___81_668.umax_heuristic_ok);
                         tcenv = (uu___81_668.tcenv);
                         wl_implicits = (imp :: (wl.wl_implicits));
                         repr_subcomp_allowed =
                           (uu___81_668.repr_subcomp_allowed)
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
            let uu___87_701 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___87_701.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___87_701.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___87_701.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___87_701.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___87_701.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___87_701.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___87_701.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___87_701.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___87_701.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___87_701.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___87_701.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___87_701.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___87_701.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___87_701.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___87_701.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___87_701.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___87_701.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___87_701.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___87_701.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___87_701.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___87_701.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___87_701.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___87_701.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___87_701.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___87_701.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___87_701.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___87_701.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___87_701.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___87_701.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___87_701.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___87_701.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___87_701.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___87_701.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___87_701.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___87_701.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___87_701.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___87_701.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___87_701.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___87_701.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___87_701.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___87_701.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___87_701.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___87_701.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___87_701.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___87_701.FStar_TypeChecker_Env.erasable_types_tab)
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
    let uu___151_1296 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___151_1296.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___151_1296.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___151_1296.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___151_1296.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___151_1296.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___151_1296.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___151_1296.FStar_TypeChecker_Common.rank)
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
          (let uu___163_1348 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___163_1348.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___163_1348.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___163_1348.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___163_1348.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___163_1348.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___163_1348.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___163_1348.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___163_1348.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___163_1348.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___167_1356 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___167_1356.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___167_1356.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___167_1356.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___167_1356.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___167_1356.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___167_1356.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___167_1356.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___167_1356.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___167_1356.FStar_TypeChecker_Common.rank)
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
        let uu___260_1881 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___260_1881.wl_deferred);
          ctr = (uu___260_1881.ctr);
          defer_ok = (uu___260_1881.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___260_1881.umax_heuristic_ok);
          tcenv = (uu___260_1881.tcenv);
          wl_implicits = (uu___260_1881.wl_implicits);
          repr_subcomp_allowed = (uu___260_1881.repr_subcomp_allowed)
        }
  
let wl_of_guard :
  'uuuuuu1889 .
    FStar_TypeChecker_Env.env ->
      ('uuuuuu1889 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___264_1912 = empty_worklist env  in
      let uu____1913 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1913;
        wl_deferred = (uu___264_1912.wl_deferred);
        ctr = (uu___264_1912.ctr);
        defer_ok = (uu___264_1912.defer_ok);
        smt_ok = (uu___264_1912.smt_ok);
        umax_heuristic_ok = (uu___264_1912.umax_heuristic_ok);
        tcenv = (uu___264_1912.tcenv);
        wl_implicits = (uu___264_1912.wl_implicits);
        repr_subcomp_allowed = (uu___264_1912.repr_subcomp_allowed)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___269_1934 = wl  in
        {
          attempting = (uu___269_1934.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___269_1934.ctr);
          defer_ok = (uu___269_1934.defer_ok);
          smt_ok = (uu___269_1934.smt_ok);
          umax_heuristic_ok = (uu___269_1934.umax_heuristic_ok);
          tcenv = (uu___269_1934.tcenv);
          wl_implicits = (uu___269_1934.wl_implicits);
          repr_subcomp_allowed = (uu___269_1934.repr_subcomp_allowed)
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
      (let uu___277_1980 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___277_1980.wl_deferred);
         ctr = (uu___277_1980.ctr);
         defer_ok = (uu___277_1980.defer_ok);
         smt_ok = (uu___277_1980.smt_ok);
         umax_heuristic_ok = (uu___277_1980.umax_heuristic_ok);
         tcenv = (uu___277_1980.tcenv);
         wl_implicits = (uu___277_1980.wl_implicits);
         repr_subcomp_allowed = (uu___277_1980.repr_subcomp_allowed)
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
                      (let uu___360_2644 = wl  in
                       {
                         attempting = (uu___360_2644.attempting);
                         wl_deferred = (uu___360_2644.wl_deferred);
                         ctr = (uu___360_2644.ctr);
                         defer_ok = (uu___360_2644.defer_ok);
                         smt_ok = (uu___360_2644.smt_ok);
                         umax_heuristic_ok =
                           (uu___360_2644.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___360_2644.wl_implicits);
                         repr_subcomp_allowed =
                           (uu___360_2644.repr_subcomp_allowed)
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
                    let uu___466_3286 = x  in
                    let uu____3287 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___466_3286.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___466_3286.FStar_Syntax_Syntax.index);
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
             (let uu___735_5673 = wl1  in
              {
                attempting = (uu___735_5673.attempting);
                wl_deferred = (uu___735_5673.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___735_5673.defer_ok);
                smt_ok = (uu___735_5673.smt_ok);
                umax_heuristic_ok = (uu___735_5673.umax_heuristic_ok);
                tcenv = (uu___735_5673.tcenv);
                wl_implicits = (uu___735_5673.wl_implicits);
                repr_subcomp_allowed = (uu___735_5673.repr_subcomp_allowed)
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
        (let uu___743_5711 = wl  in
         {
           attempting = (uu___743_5711.attempting);
           wl_deferred = (uu___743_5711.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___743_5711.defer_ok);
           smt_ok = (uu___743_5711.smt_ok);
           umax_heuristic_ok = (uu___743_5711.umax_heuristic_ok);
           tcenv = (uu___743_5711.tcenv);
           wl_implicits = (uu___743_5711.wl_implicits);
           repr_subcomp_allowed = (uu___743_5711.repr_subcomp_allowed)
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
      let uu___1232_8726 = p  in
      let uu____8729 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8730 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1232_8726.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8729;
        FStar_TypeChecker_Common.relation =
          (uu___1232_8726.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8730;
        FStar_TypeChecker_Common.element =
          (uu___1232_8726.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1232_8726.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1232_8726.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1232_8726.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1232_8726.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1232_8726.FStar_TypeChecker_Common.rank)
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
                            (let uu___1283_9069 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1283_9069.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1283_9069.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1283_9069.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1283_9069.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1283_9069.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1283_9069.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1283_9069.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1283_9069.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1283_9069.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9072,FStar_Syntax_Syntax.Tm_type uu____9073)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1283_9089 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1283_9089.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1283_9089.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1283_9089.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1283_9089.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1283_9089.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1283_9089.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1283_9089.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1283_9089.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1283_9089.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9092,FStar_Syntax_Syntax.Tm_uvar uu____9093)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1283_9109 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1283_9109.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1283_9109.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1283_9109.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1283_9109.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1283_9109.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1283_9109.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1283_9109.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1283_9109.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1283_9109.FStar_TypeChecker_Common.rank)
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
                             (let uu___1303_9178 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1303_9178.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1303_9178.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1303_9178.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1303_9178.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1303_9178.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1303_9178.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1303_9178.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1303_9178.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1303_9178.FStar_TypeChecker_Common.loc);
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
              (let uu___1307_9189 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1307_9189.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1307_9189.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1307_9189.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1307_9189.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1307_9189.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1307_9189.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1307_9189.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1307_9189.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1307_9189.FStar_TypeChecker_Common.loc);
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
                          let uu___1635_11317 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1635_11317.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1635_11317.FStar_Syntax_Syntax.index);
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
                          (((let uu___1641_11345 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1641_11345.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1641_11345.FStar_Syntax_Syntax.index);
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
             let uu___1668_11822 = probs  in
             {
               attempting = tl;
               wl_deferred = (uu___1668_11822.wl_deferred);
               ctr = (uu___1668_11822.ctr);
               defer_ok = (uu___1668_11822.defer_ok);
               smt_ok = (uu___1668_11822.smt_ok);
               umax_heuristic_ok = (uu___1668_11822.umax_heuristic_ok);
               tcenv = (uu___1668_11822.tcenv);
               wl_implicits = (uu___1668_11822.wl_implicits);
               repr_subcomp_allowed = (uu___1668_11822.repr_subcomp_allowed)
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
                           (let uu___1680_11847 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1680_11847.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1680_11847.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1680_11847.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1680_11847.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1680_11847.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1680_11847.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1680_11847.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1680_11847.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1680_11847.FStar_TypeChecker_Common.rank)
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
                            let uu___1698_12074 = probs  in
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
                              ctr = (uu___1698_12074.ctr);
                              defer_ok = (uu___1698_12074.defer_ok);
                              smt_ok = (uu___1698_12074.smt_ok);
                              umax_heuristic_ok =
                                (uu___1698_12074.umax_heuristic_ok);
                              tcenv = (uu___1698_12074.tcenv);
                              wl_implicits = (uu___1698_12074.wl_implicits);
                              repr_subcomp_allowed =
                                (uu___1698_12074.repr_subcomp_allowed)
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
                                                  let uu___1852_12900 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1852_12900.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1852_12900.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1852_12900.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1852_12900.repr_subcomp_allowed)
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
                                                        ((let uu___1861_12918
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1861_12918.attempting);
                                                            wl_deferred =
                                                              (uu___1861_12918.wl_deferred);
                                                            ctr =
                                                              (uu___1861_12918.ctr);
                                                            defer_ok =
                                                              (uu___1861_12918.defer_ok);
                                                            smt_ok =
                                                              (uu___1861_12918.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1861_12918.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1861_12918.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps);
                                                            repr_subcomp_allowed
                                                              =
                                                              (uu___1861_12918.repr_subcomp_allowed)
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
                              ((let uu___1963_13642 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1963_13642.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1963_13642.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1963_13642.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1963_13642.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1963_13642.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1963_13642.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1963_13642.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1963_13642.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1963_13642.FStar_TypeChecker_Common.rank)
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
                                                    let uu___2023_13984 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2023_13984.wl_deferred);
                                                      ctr =
                                                        (uu___2023_13984.ctr);
                                                      defer_ok =
                                                        (uu___2023_13984.defer_ok);
                                                      smt_ok =
                                                        (uu___2023_13984.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2023_13984.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2023_13984.tcenv);
                                                      wl_implicits =
                                                        (uu___2023_13984.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2023_13984.repr_subcomp_allowed)
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
                                                    (let uu___2028_13993 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2028_13993.wl_deferred);
                                                       ctr =
                                                         (uu___2028_13993.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2028_13993.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2028_13993.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2028_13993.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2028_13993.repr_subcomp_allowed)
                                                     })
                                                   in
                                                match uu____13991 with
                                                | Success (uu____13995,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2034_13998 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2034_13998.wl_deferred);
                                                        ctr =
                                                          (uu___2034_13998.ctr);
                                                        defer_ok =
                                                          (uu___2034_13998.defer_ok);
                                                        smt_ok =
                                                          (uu___2034_13998.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2034_13998.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2034_13998.tcenv);
                                                        wl_implicits =
                                                          (uu___2034_13998.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2034_13998.repr_subcomp_allowed)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2037_14000 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2037_14000.attempting);
                                                        wl_deferred =
                                                          (uu___2037_14000.wl_deferred);
                                                        ctr =
                                                          (uu___2037_14000.ctr);
                                                        defer_ok =
                                                          (uu___2037_14000.defer_ok);
                                                        smt_ok =
                                                          (uu___2037_14000.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2037_14000.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2037_14000.tcenv);
                                                        wl_implicits =
                                                          (FStar_List.append
                                                             wl'.wl_implicits
                                                             imps);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2037_14000.repr_subcomp_allowed)
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
                                 let nodec flags =
                                   FStar_List.filter
                                     (fun uu___25_14751  ->
                                        match uu___25_14751 with
                                        | FStar_Syntax_Syntax.DECREASES
                                            uu____14753 -> false
                                        | uu____14757 -> true) flags
                                    in
                                 let ct' =
                                   let uu___2154_14760 = ct  in
                                   let uu____14761 =
                                     let uu____14764 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14764
                                      in
                                   let uu____14779 = FStar_List.tl out_args
                                      in
                                   let uu____14796 =
                                     nodec ct.FStar_Syntax_Syntax.flags  in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2154_14760.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2154_14760.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14761;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14779;
                                     FStar_Syntax_Syntax.flags = uu____14796
                                   }  in
                                 ((let uu___2157_14800 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2157_14800.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2157_14800.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14803 =
                        FStar_Syntax_Util.arrow_formals_comp arrow  in
                      (match uu____14803 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14841 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14841 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14852 =
                                          let uu____14857 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14857)  in
                                        TERM uu____14852  in
                                      let uu____14858 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14858 with
                                       | (sub_prob,wl3) ->
                                           let uu____14872 =
                                             let uu____14873 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14873
                                              in
                                           solve env uu____14872))
                             | (x,imp)::formals2 ->
                                 let uu____14895 =
                                   let uu____14902 =
                                     let uu____14905 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14905
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14902 wl1
                                    in
                                 (match uu____14895 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14926 =
                                          let uu____14929 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14929
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14926 u_x
                                         in
                                      let uu____14930 =
                                        let uu____14933 =
                                          let uu____14936 =
                                            let uu____14937 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14937, imp)  in
                                          [uu____14936]  in
                                        FStar_List.append bs_terms
                                          uu____14933
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14930 formals2 wl2)
                              in
                           let uu____14964 = occurs_check u_lhs arrow  in
                           (match uu____14964 with
                            | (uu____14977,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14993 =
                                    mklstr
                                      (fun uu____14998  ->
                                         let uu____14999 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14999)
                                     in
                                  giveup_or_defer env orig wl uu____14993
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
              (let uu____15032 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____15032
               then
                 let uu____15037 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____15040 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15037 (rel_to_string (p_rel orig)) uu____15040
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15171 = rhs wl1 scope env1 subst  in
                     (match uu____15171 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15194 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15194
                            then
                              let uu____15199 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15199
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15277 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15277 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2227_15279 = hd1  in
                       let uu____15280 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2227_15279.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2227_15279.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15280
                       }  in
                     let hd21 =
                       let uu___2230_15284 = hd2  in
                       let uu____15285 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2230_15284.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2230_15284.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15285
                       }  in
                     let uu____15288 =
                       let uu____15293 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15293
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15288 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst1 =
                            let uu____15316 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15316
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15323 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1
                             in
                          (match uu____15323 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15395 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15395
                                  in
                               ((let uu____15413 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15413
                                 then
                                   let uu____15418 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15420 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15418
                                     uu____15420
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____15455 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15491 = aux wl [] env [] bs1 bs2  in
               match uu____15491 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15550 = attempt sub_probs wl2  in
                   solve env1 uu____15550)

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
            let uu___2268_15570 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2268_15570.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2268_15570.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2268_15570.repr_subcomp_allowed)
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15582 = try_solve env wl'  in
          match uu____15582 with
          | Success (uu____15583,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2277_15587 = wl  in
                  {
                    attempting = (uu___2277_15587.attempting);
                    wl_deferred = (uu___2277_15587.wl_deferred);
                    ctr = (uu___2277_15587.ctr);
                    defer_ok = (uu___2277_15587.defer_ok);
                    smt_ok = (uu___2277_15587.smt_ok);
                    umax_heuristic_ok = (uu___2277_15587.umax_heuristic_ok);
                    tcenv = (uu___2277_15587.tcenv);
                    wl_implicits = (FStar_List.append wl.wl_implicits imps);
                    repr_subcomp_allowed =
                      (uu___2277_15587.repr_subcomp_allowed)
                  }  in
                solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____15596 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15596 wl)

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
              let uu____15610 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15610 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15644 = lhs1  in
              match uu____15644 with
              | (uu____15647,ctx_u,uu____15649) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15657 ->
                        let uu____15658 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15658 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15707 = quasi_pattern env1 lhs1  in
              match uu____15707 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15741) ->
                  let uu____15746 = lhs1  in
                  (match uu____15746 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15761 = occurs_check ctx_u rhs1  in
                       (match uu____15761 with
                        | (uvars,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15812 =
                                let uu____15820 =
                                  let uu____15822 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15822
                                   in
                                FStar_Util.Inl uu____15820  in
                              (uu____15812, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15850 =
                                 let uu____15852 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15852  in
                               if uu____15850
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15879 =
                                    let uu____15887 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15887  in
                                  let uu____15893 =
                                    restrict_all_uvars ctx_u uvars wl1  in
                                  (uu____15879, uu____15893)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15937 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15937 with
              | (rhs_hd,args) ->
                  let uu____15980 = FStar_Util.prefix args  in
                  (match uu____15980 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____16052 = lhs1  in
                       (match uu____16052 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____16056 =
                              let uu____16067 =
                                let uu____16074 =
                                  let uu____16077 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____16077
                                   in
                                copy_uvar u_lhs [] uu____16074 wl1  in
                              match uu____16067 with
                              | (uu____16104,t_last_arg,wl2) ->
                                  let uu____16107 =
                                    let uu____16114 =
                                      let uu____16115 =
                                        let uu____16124 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____16124]  in
                                      FStar_List.append bs_lhs uu____16115
                                       in
                                    copy_uvar u_lhs uu____16114 t_res_lhs wl2
                                     in
                                  (match uu____16107 with
                                   | (uu____16159,lhs',wl3) ->
                                       let uu____16162 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16162 with
                                        | (uu____16179,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____16056 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16200 =
                                     let uu____16201 =
                                       let uu____16206 =
                                         let uu____16207 =
                                           let uu____16210 =
                                             let uu____16215 =
                                               let uu____16216 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16216]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16215
                                              in
                                           uu____16210
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16207
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16206)  in
                                     TERM uu____16201  in
                                   [uu____16200]  in
                                 let uu____16241 =
                                   let uu____16248 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16248 with
                                   | (p1,wl3) ->
                                       let uu____16268 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16268 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16241 with
                                  | (sub_probs,wl3) ->
                                      let uu____16300 =
                                        let uu____16301 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16301  in
                                      solve env1 uu____16300))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16335 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16335 with
                | (uu____16353,args) ->
                    (match args with | [] -> false | uu____16389 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16408 =
                  let uu____16409 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16409.FStar_Syntax_Syntax.n  in
                match uu____16408 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16413 -> true
                | uu____16429 -> false  in
              let uu____16431 = quasi_pattern env1 lhs1  in
              match uu____16431 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    mklstr
                      (fun uu____16450  ->
                         let uu____16451 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16451)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16460 = is_app rhs1  in
                  if uu____16460
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16465 = is_arrow rhs1  in
                     if uu____16465
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          mklstr
                            (fun uu____16478  ->
                               let uu____16479 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16479)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16483 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16483
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16489 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16489
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16494 = lhs  in
                (match uu____16494 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16498 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16498 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16516 =
                              let uu____16520 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16520
                               in
                            FStar_All.pipe_right uu____16516
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16541 = occurs_check ctx_uv rhs1  in
                          (match uu____16541 with
                           | (uvars,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16570 =
                                   let uu____16571 =
                                     let uu____16573 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16573
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16571
                                    in
                                 giveup_or_defer env orig wl uu____16570
                               else
                                 (let uu____16581 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16581
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars wl  in
                                    let uu____16588 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16588
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         mklstr
                                           (fun uu____16604  ->
                                              let uu____16605 =
                                                names_to_string1 fvs2  in
                                              let uu____16607 =
                                                names_to_string1 fvs1  in
                                              let uu____16609 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16605 uu____16607
                                                uu____16609)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16621 ->
                          if wl.defer_ok
                          then
                            let uu____16625 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16625
                          else
                            (let uu____16630 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16630 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16656 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16656
                             | (FStar_Util.Inl msg,uu____16658) ->
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
                  let uu____16676 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16676
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16682 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16682
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16704 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16704
                else
                  (let uu____16709 =
                     let uu____16726 = quasi_pattern env lhs  in
                     let uu____16733 = quasi_pattern env rhs  in
                     (uu____16726, uu____16733)  in
                   match uu____16709 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16776 = lhs  in
                       (match uu____16776 with
                        | ({ FStar_Syntax_Syntax.n = uu____16777;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16779;_},u_lhs,uu____16781)
                            ->
                            let uu____16784 = rhs  in
                            (match uu____16784 with
                             | (uu____16785,u_rhs,uu____16787) ->
                                 let uu____16788 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16788
                                 then
                                   let uu____16795 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16795
                                 else
                                   (let uu____16798 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16798 with
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
                                        let uu____16830 =
                                          let uu____16837 =
                                            let uu____16840 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16840
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16837
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16830 with
                                         | (uu____16852,w,wl1) ->
                                             let w_app =
                                               let uu____16858 =
                                                 let uu____16863 =
                                                   FStar_List.map
                                                     (fun uu____16874  ->
                                                        match uu____16874
                                                        with
                                                        | (z,uu____16882) ->
                                                            let uu____16887 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16887) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16863
                                                  in
                                               uu____16858
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16889 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16889
                                               then
                                                 let uu____16894 =
                                                   let uu____16898 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16900 =
                                                     let uu____16904 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16906 =
                                                       let uu____16910 =
                                                         term_to_string w  in
                                                       let uu____16912 =
                                                         let uu____16916 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16925 =
                                                           let uu____16929 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16938 =
                                                             let uu____16942
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16942]
                                                              in
                                                           uu____16929 ::
                                                             uu____16938
                                                            in
                                                         uu____16916 ::
                                                           uu____16925
                                                          in
                                                       uu____16910 ::
                                                         uu____16912
                                                        in
                                                     uu____16904 ::
                                                       uu____16906
                                                      in
                                                   uu____16898 :: uu____16900
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16894
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16959 =
                                                     let uu____16964 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16964)  in
                                                   TERM uu____16959  in
                                                 let uu____16965 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16965
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16973 =
                                                        let uu____16978 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16978)
                                                         in
                                                      TERM uu____16973  in
                                                    [s1; s2])
                                                  in
                                               let uu____16979 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16979))))))
                   | uu____16980 ->
                       let uu____16997 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16997)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17051 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____17051
            then
              let uu____17056 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17058 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17060 = FStar_Syntax_Print.term_to_string t2  in
              let uu____17062 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17056 uu____17058 uu____17060 uu____17062
            else ());
           (let uu____17073 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17073 with
            | (head1,args1) ->
                let uu____17116 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17116 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17186 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17186 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17191 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17191)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17212 =
                         mklstr
                           (fun uu____17223  ->
                              let uu____17224 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17226 = args_to_string args1  in
                              let uu____17230 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17232 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17224 uu____17226 uu____17230
                                uu____17232)
                          in
                       giveup env1 uu____17212 orig
                     else
                       (let uu____17239 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17244 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17244 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17239
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2533_17248 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2533_17248.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2533_17248.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2533_17248.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2533_17248.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2533_17248.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2533_17248.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2533_17248.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2533_17248.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17258 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17258
                                    else solve env1 wl2))
                        else
                          (let uu____17263 = base_and_refinement env1 t1  in
                           match uu____17263 with
                           | (base1,refinement1) ->
                               let uu____17288 = base_and_refinement env1 t2
                                  in
                               (match uu____17288 with
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
                                           let uu____17453 =
                                             FStar_List.fold_right
                                               (fun uu____17493  ->
                                                  fun uu____17494  ->
                                                    match (uu____17493,
                                                            uu____17494)
                                                    with
                                                    | (((a1,uu____17546),
                                                        (a2,uu____17548)),
                                                       (probs,wl3)) ->
                                                        let uu____17597 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17597
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17453 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17640 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17640
                                                 then
                                                   let uu____17645 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17645
                                                 else ());
                                                (let uu____17651 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17651
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
                                                    (let uu____17678 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17678 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17694 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17694
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17702 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17702))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17727 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17727 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17743 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17743
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17751 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17751)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17779 =
                                           match uu____17779 with
                                           | (prob,reason) ->
                                               ((let uu____17796 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17796
                                                 then
                                                   let uu____17801 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17803 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____17801 uu____17803
                                                 else ());
                                                (let uu____17809 =
                                                   let uu____17818 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17821 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17818, uu____17821)
                                                    in
                                                 match uu____17809 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17834 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17834 with
                                                      | (head1',uu____17852)
                                                          ->
                                                          let uu____17877 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17877
                                                           with
                                                           | (head2',uu____17895)
                                                               ->
                                                               let uu____17920
                                                                 =
                                                                 let uu____17925
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17926
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17925,
                                                                   uu____17926)
                                                                  in
                                                               (match uu____17920
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17928
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17928
                                                                    then
                                                                    let uu____17933
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17935
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17937
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17939
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17933
                                                                    uu____17935
                                                                    uu____17937
                                                                    uu____17939
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17944
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2621_17952
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2621_17952.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2621_17952.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2621_17952.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2621_17952.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2621_17952.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2621_17952.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2621_17952.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2621_17952.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17954
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17954
                                                                    then
                                                                    let uu____17959
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17959
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17964 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17976 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17976 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17984 =
                                             let uu____17985 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17985.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17984 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17990 -> false  in
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
                                          | uu____17993 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17996 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2641_18032 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2641_18032.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2641_18032.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2641_18032.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2641_18032.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2641_18032.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2641_18032.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2641_18032.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2641_18032.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18108 = destruct_flex_t scrutinee wl1  in
             match uu____18108 with
             | ((_t,uv,_args),wl2) ->
                 let uu____18119 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18119 with
                  | (xs,pat_term,uu____18135,uu____18136) ->
                      let uu____18141 =
                        FStar_List.fold_left
                          (fun uu____18164  ->
                             fun x  ->
                               match uu____18164 with
                               | (subst,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18185 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18185 with
                                    | (uu____18204,u,wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst  in
                                        (subst1, wl4))) ([], wl2) xs
                         in
                      (match uu____18141 with
                       | (subst,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term  in
                           let uu____18225 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18225 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2681_18242 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2681_18242.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2681_18242.umax_heuristic_ok);
                                    tcenv = (uu___2681_18242.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2681_18242.repr_subcomp_allowed)
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18253 = solve env1 wl'  in
                                (match uu____18253 with
                                 | Success (uu____18256,imps) ->
                                     let wl'1 =
                                       let uu___2689_18259 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2689_18259.wl_deferred);
                                         ctr = (uu___2689_18259.ctr);
                                         defer_ok =
                                           (uu___2689_18259.defer_ok);
                                         smt_ok = (uu___2689_18259.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2689_18259.umax_heuristic_ok);
                                         tcenv = (uu___2689_18259.tcenv);
                                         wl_implicits =
                                           (uu___2689_18259.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2689_18259.repr_subcomp_allowed)
                                       }  in
                                     let uu____18260 = solve env1 wl'1  in
                                     (match uu____18260 with
                                      | Success (uu____18263,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2697_18267 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2697_18267.attempting);
                                                 wl_deferred =
                                                   (uu___2697_18267.wl_deferred);
                                                 ctr = (uu___2697_18267.ctr);
                                                 defer_ok =
                                                   (uu___2697_18267.defer_ok);
                                                 smt_ok =
                                                   (uu___2697_18267.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2697_18267.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2697_18267.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'));
                                                 repr_subcomp_allowed =
                                                   (uu___2697_18267.repr_subcomp_allowed)
                                               })))
                                      | Failed uu____18268 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18274 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18297 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18297
                 then
                   let uu____18302 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18304 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18302 uu____18304
                 else ());
                (let uu____18309 =
                   let uu____18330 =
                     let uu____18339 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18339)  in
                   let uu____18346 =
                     let uu____18355 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18355)  in
                   (uu____18330, uu____18346)  in
                 match uu____18309 with
                 | ((uu____18385,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18388;
                                   FStar_Syntax_Syntax.vars = uu____18389;_}),
                    (s,t)) ->
                     let uu____18460 =
                       let uu____18462 = is_flex scrutinee  in
                       Prims.op_Negation uu____18462  in
                     if uu____18460
                     then
                       ((let uu____18473 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18473
                         then
                           let uu____18478 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18478
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18497 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18497
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18512 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18512
                           then
                             let uu____18517 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18519 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18517 uu____18519
                           else ());
                          (let pat_discriminates uu___26_18544 =
                             match uu___26_18544 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18560;
                                  FStar_Syntax_Syntax.p = uu____18561;_},FStar_Pervasives_Native.None
                                ,uu____18562) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18576;
                                  FStar_Syntax_Syntax.p = uu____18577;_},FStar_Pervasives_Native.None
                                ,uu____18578) -> true
                             | uu____18605 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18708 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18708 with
                                       | (uu____18710,uu____18711,t') ->
                                           let uu____18729 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18729 with
                                            | (FullMatch ,uu____18741) ->
                                                true
                                            | (HeadMatch
                                               uu____18755,uu____18756) ->
                                                true
                                            | uu____18771 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18808 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18808
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18819 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18819 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18907,uu____18908) ->
                                       branches1
                                   | uu____19053 -> branches  in
                                 let uu____19108 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19117 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19117 with
                                        | (p,uu____19121,uu____19122) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19151  ->
                                      FStar_Util.Inr uu____19151) uu____19108))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19181 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19181 with
                                | (p,uu____19190,e) ->
                                    ((let uu____19209 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19209
                                      then
                                        let uu____19214 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19216 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19214 uu____19216
                                      else ());
                                     (let uu____19221 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____19236  ->
                                           FStar_Util.Inr uu____19236)
                                        uu____19221)))))
                 | ((s,t),(uu____19239,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19242;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19243;_}))
                     ->
                     let uu____19312 =
                       let uu____19314 = is_flex scrutinee  in
                       Prims.op_Negation uu____19314  in
                     if uu____19312
                     then
                       ((let uu____19325 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19325
                         then
                           let uu____19330 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19330
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19349 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19349
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19364 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19364
                           then
                             let uu____19369 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19371 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19369 uu____19371
                           else ());
                          (let pat_discriminates uu___26_19396 =
                             match uu___26_19396 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19412;
                                  FStar_Syntax_Syntax.p = uu____19413;_},FStar_Pervasives_Native.None
                                ,uu____19414) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19428;
                                  FStar_Syntax_Syntax.p = uu____19429;_},FStar_Pervasives_Native.None
                                ,uu____19430) -> true
                             | uu____19457 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19560 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19560 with
                                       | (uu____19562,uu____19563,t') ->
                                           let uu____19581 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19581 with
                                            | (FullMatch ,uu____19593) ->
                                                true
                                            | (HeadMatch
                                               uu____19607,uu____19608) ->
                                                true
                                            | uu____19623 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19660 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19660
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19671 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19671 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19759,uu____19760) ->
                                       branches1
                                   | uu____19905 -> branches  in
                                 let uu____19960 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19969 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19969 with
                                        | (p,uu____19973,uu____19974) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____20003  ->
                                      FStar_Util.Inr uu____20003) uu____19960))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20033 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20033 with
                                | (p,uu____20042,e) ->
                                    ((let uu____20061 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20061
                                      then
                                        let uu____20066 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20068 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20066 uu____20068
                                      else ());
                                     (let uu____20073 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____20088  ->
                                           FStar_Util.Inr uu____20088)
                                        uu____20073)))))
                 | uu____20089 ->
                     ((let uu____20111 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20111
                       then
                         let uu____20116 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20118 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20116 uu____20118
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20164 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20164
            then
              let uu____20169 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20171 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20173 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20175 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20169 uu____20171 uu____20173 uu____20175
            else ());
           (let uu____20180 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20180 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20211,uu____20212) ->
                     let rec may_relate head =
                       let uu____20240 =
                         let uu____20241 = FStar_Syntax_Subst.compress head
                            in
                         uu____20241.FStar_Syntax_Syntax.n  in
                       match uu____20240 with
                       | FStar_Syntax_Syntax.Tm_name uu____20245 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20247 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20272 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20272 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20274 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20277
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20278 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20281,uu____20282) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20324) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20330) ->
                           may_relate t
                       | uu____20335 -> false  in
                     let uu____20337 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20337 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20350 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20350
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20360 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20360
                          then
                            let uu____20363 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20363 with
                             | (guard,wl2) ->
                                 let uu____20370 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20370)
                          else
                            (let uu____20373 =
                               mklstr
                                 (fun uu____20384  ->
                                    let uu____20385 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20387 =
                                      let uu____20389 =
                                        let uu____20393 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20393
                                          (fun x  ->
                                             let uu____20400 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20400)
                                         in
                                      FStar_Util.dflt "" uu____20389  in
                                    let uu____20405 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20407 =
                                      let uu____20409 =
                                        let uu____20413 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20413
                                          (fun x  ->
                                             let uu____20420 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20420)
                                         in
                                      FStar_Util.dflt "" uu____20409  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20385 uu____20387 uu____20405
                                      uu____20407)
                                in
                             giveup env1 uu____20373 orig))
                 | (HeadMatch (true ),uu____20426) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20441 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20441 with
                        | (guard,wl2) ->
                            let uu____20448 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20448)
                     else
                       (let uu____20451 =
                          mklstr
                            (fun uu____20458  ->
                               let uu____20459 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20461 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20459 uu____20461)
                           in
                        giveup env1 uu____20451 orig)
                 | (uu____20464,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2872_20478 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2872_20478.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2872_20478.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2872_20478.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2872_20478.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2872_20478.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2872_20478.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2872_20478.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2872_20478.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20505 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20505
          then
            let uu____20508 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20508
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20514 =
                let uu____20517 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20517  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20514 t1);
             (let uu____20536 =
                let uu____20539 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20539  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20536 t2);
             (let uu____20558 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20558
              then
                let uu____20562 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20564 =
                  let uu____20566 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20568 =
                    let uu____20570 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20570  in
                  Prims.op_Hat uu____20566 uu____20568  in
                let uu____20573 =
                  let uu____20575 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20577 =
                    let uu____20579 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20579  in
                  Prims.op_Hat uu____20575 uu____20577  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20562 uu____20564 uu____20573
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20586,uu____20587) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20603,FStar_Syntax_Syntax.Tm_delayed uu____20604) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20620,uu____20621) ->
                  let uu____20648 =
                    let uu___2903_20649 = problem  in
                    let uu____20650 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2903_20649.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20650;
                      FStar_TypeChecker_Common.relation =
                        (uu___2903_20649.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2903_20649.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2903_20649.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2903_20649.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2903_20649.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2903_20649.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2903_20649.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2903_20649.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20648 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20651,uu____20652) ->
                  let uu____20659 =
                    let uu___2909_20660 = problem  in
                    let uu____20661 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2909_20660.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20661;
                      FStar_TypeChecker_Common.relation =
                        (uu___2909_20660.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2909_20660.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2909_20660.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2909_20660.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2909_20660.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2909_20660.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2909_20660.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2909_20660.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20659 wl
              | (uu____20662,FStar_Syntax_Syntax.Tm_ascribed uu____20663) ->
                  let uu____20690 =
                    let uu___2915_20691 = problem  in
                    let uu____20692 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2915_20691.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2915_20691.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2915_20691.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20692;
                      FStar_TypeChecker_Common.element =
                        (uu___2915_20691.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2915_20691.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2915_20691.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2915_20691.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2915_20691.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2915_20691.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20690 wl
              | (uu____20693,FStar_Syntax_Syntax.Tm_meta uu____20694) ->
                  let uu____20701 =
                    let uu___2921_20702 = problem  in
                    let uu____20703 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2921_20702.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2921_20702.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2921_20702.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20703;
                      FStar_TypeChecker_Common.element =
                        (uu___2921_20702.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2921_20702.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2921_20702.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2921_20702.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2921_20702.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2921_20702.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20701 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20705),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20707)) ->
                  let uu____20716 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20716
              | (FStar_Syntax_Syntax.Tm_bvar uu____20717,uu____20718) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20720,FStar_Syntax_Syntax.Tm_bvar uu____20721) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___27_20791 =
                    match uu___27_20791 with
                    | [] -> c
                    | bs ->
                        let uu____20819 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20819
                     in
                  let uu____20830 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20830 with
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
                                    let uu____20979 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20979
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
                  let mk_t t l uu___28_21068 =
                    match uu___28_21068 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21110 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21110 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst  ->
                                  let uu____21255 =
                                    FStar_Syntax_Subst.subst subst tbody11
                                     in
                                  let uu____21256 =
                                    FStar_Syntax_Subst.subst subst tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21255
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21256 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21258,uu____21259) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21290 -> true
                    | uu____21310 -> false  in
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
                      (let uu____21370 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3023_21378 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3023_21378.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3023_21378.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3023_21378.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3023_21378.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3023_21378.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3023_21378.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3023_21378.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3023_21378.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3023_21378.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3023_21378.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3023_21378.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3023_21378.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3023_21378.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3023_21378.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3023_21378.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3023_21378.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3023_21378.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3023_21378.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3023_21378.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3023_21378.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3023_21378.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3023_21378.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3023_21378.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3023_21378.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3023_21378.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3023_21378.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3023_21378.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3023_21378.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3023_21378.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3023_21378.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3023_21378.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3023_21378.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3023_21378.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3023_21378.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3023_21378.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3023_21378.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3023_21378.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3023_21378.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3023_21378.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3023_21378.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3023_21378.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3023_21378.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3023_21378.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21370 with
                       | (uu____21383,ty,uu____21385) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21394 =
                                 let uu____21395 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21395.FStar_Syntax_Syntax.n  in
                               match uu____21394 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21398 ->
                                   let uu____21405 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21405
                               | uu____21406 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21409 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21409
                             then
                               let uu____21414 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21416 =
                                 let uu____21418 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21418
                                  in
                               let uu____21419 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21414 uu____21416 uu____21419
                             else ());
                            r1))
                     in
                  let uu____21424 =
                    let uu____21441 = maybe_eta t1  in
                    let uu____21448 = maybe_eta t2  in
                    (uu____21441, uu____21448)  in
                  (match uu____21424 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3044_21490 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3044_21490.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3044_21490.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3044_21490.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3044_21490.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3044_21490.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3044_21490.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3044_21490.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3044_21490.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21511 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21511
                       then
                         let uu____21514 = destruct_flex_t not_abs wl  in
                         (match uu____21514 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3061_21531 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3061_21531.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3061_21531.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3061_21531.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3061_21531.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3061_21531.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3061_21531.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3061_21531.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3061_21531.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21534 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21534 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21557 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21557
                       then
                         let uu____21560 = destruct_flex_t not_abs wl  in
                         (match uu____21560 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3061_21577 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3061_21577.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3061_21577.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3061_21577.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3061_21577.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3061_21577.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3061_21577.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3061_21577.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3061_21577.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21580 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21580 orig))
                   | uu____21583 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21601,FStar_Syntax_Syntax.Tm_abs uu____21602) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21633 -> true
                    | uu____21653 -> false  in
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
                      (let uu____21713 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3023_21721 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3023_21721.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3023_21721.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3023_21721.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3023_21721.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3023_21721.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3023_21721.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3023_21721.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3023_21721.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3023_21721.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3023_21721.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3023_21721.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3023_21721.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3023_21721.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3023_21721.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3023_21721.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3023_21721.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3023_21721.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3023_21721.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3023_21721.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3023_21721.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3023_21721.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3023_21721.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3023_21721.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3023_21721.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3023_21721.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3023_21721.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3023_21721.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3023_21721.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3023_21721.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3023_21721.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3023_21721.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3023_21721.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3023_21721.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3023_21721.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3023_21721.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3023_21721.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3023_21721.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3023_21721.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3023_21721.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3023_21721.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3023_21721.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3023_21721.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3023_21721.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21713 with
                       | (uu____21726,ty,uu____21728) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21737 =
                                 let uu____21738 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21738.FStar_Syntax_Syntax.n  in
                               match uu____21737 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21741 ->
                                   let uu____21748 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21748
                               | uu____21749 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21752 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21752
                             then
                               let uu____21757 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21759 =
                                 let uu____21761 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21761
                                  in
                               let uu____21762 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21757 uu____21759 uu____21762
                             else ());
                            r1))
                     in
                  let uu____21767 =
                    let uu____21784 = maybe_eta t1  in
                    let uu____21791 = maybe_eta t2  in
                    (uu____21784, uu____21791)  in
                  (match uu____21767 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3044_21833 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3044_21833.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3044_21833.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3044_21833.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3044_21833.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3044_21833.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3044_21833.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3044_21833.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3044_21833.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21854 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21854
                       then
                         let uu____21857 = destruct_flex_t not_abs wl  in
                         (match uu____21857 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3061_21874 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3061_21874.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3061_21874.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3061_21874.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3061_21874.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3061_21874.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3061_21874.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3061_21874.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3061_21874.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21877 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21877 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21900 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21900
                       then
                         let uu____21903 = destruct_flex_t not_abs wl  in
                         (match uu____21903 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3061_21920 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3061_21920.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3061_21920.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3061_21920.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3061_21920.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3061_21920.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3061_21920.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3061_21920.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3061_21920.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21923 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21923 orig))
                   | uu____21926 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21956 =
                    let uu____21961 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21961 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3084_21989 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3084_21989.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3084_21989.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3086_21991 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3086_21991.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3086_21991.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21992,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3084_22007 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3084_22007.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3084_22007.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3086_22009 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3086_22009.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3086_22009.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22010 -> (x1, x2)  in
                  (match uu____21956 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____22029 = as_refinement false env t11  in
                       (match uu____22029 with
                        | (x12,phi11) ->
                            let uu____22037 = as_refinement false env t21  in
                            (match uu____22037 with
                             | (x22,phi21) ->
                                 ((let uu____22046 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22046
                                   then
                                     ((let uu____22051 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____22053 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22055 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22051
                                         uu____22053 uu____22055);
                                      (let uu____22058 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____22060 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22062 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22058
                                         uu____22060 uu____22062))
                                   else ());
                                  (let uu____22067 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____22067 with
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
                                         let uu____22138 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22138
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22150 =
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
                                         (let uu____22163 =
                                            let uu____22166 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22166
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22163
                                            (p_guard base_prob));
                                         (let uu____22185 =
                                            let uu____22188 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22188
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22185
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22207 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22207)
                                          in
                                       let has_uvars =
                                         (let uu____22212 =
                                            let uu____22214 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22214
                                             in
                                          Prims.op_Negation uu____22212) ||
                                           (let uu____22218 =
                                              let uu____22220 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22220
                                               in
                                            Prims.op_Negation uu____22218)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22224 =
                                           let uu____22229 =
                                             let uu____22238 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22238]  in
                                           mk_t_problem wl1 uu____22229 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22224 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22261 =
                                                solve env1
                                                  (let uu___3129_22263 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3129_22263.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3129_22263.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3129_22263.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3129_22263.tcenv);
                                                     wl_implicits =
                                                       (uu___3129_22263.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3129_22263.repr_subcomp_allowed)
                                                   })
                                                 in
                                              (match uu____22261 with
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
                                               | Success uu____22278 ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22287 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22287
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3142_22296 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3142_22296.attempting);
                                                         wl_deferred =
                                                           (uu___3142_22296.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3142_22296.defer_ok);
                                                         smt_ok =
                                                           (uu___3142_22296.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3142_22296.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3142_22296.tcenv);
                                                         wl_implicits =
                                                           (uu___3142_22296.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3142_22296.repr_subcomp_allowed)
                                                       }  in
                                                     let uu____22298 =
                                                       attempt [base_prob]
                                                         wl4
                                                        in
                                                     solve env1 uu____22298))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22301,FStar_Syntax_Syntax.Tm_uvar uu____22302) ->
                  let uu____22327 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22327 with
                   | (t11,wl1) ->
                       let uu____22334 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22334 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22343;
                    FStar_Syntax_Syntax.pos = uu____22344;
                    FStar_Syntax_Syntax.vars = uu____22345;_},uu____22346),FStar_Syntax_Syntax.Tm_uvar
                 uu____22347) ->
                  let uu____22396 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22396 with
                   | (t11,wl1) ->
                       let uu____22403 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22403 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22412,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22413;
                    FStar_Syntax_Syntax.pos = uu____22414;
                    FStar_Syntax_Syntax.vars = uu____22415;_},uu____22416))
                  ->
                  let uu____22465 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22465 with
                   | (t11,wl1) ->
                       let uu____22472 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22472 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22481;
                    FStar_Syntax_Syntax.pos = uu____22482;
                    FStar_Syntax_Syntax.vars = uu____22483;_},uu____22484),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22485;
                    FStar_Syntax_Syntax.pos = uu____22486;
                    FStar_Syntax_Syntax.vars = uu____22487;_},uu____22488))
                  ->
                  let uu____22561 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22561 with
                   | (t11,wl1) ->
                       let uu____22568 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22568 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22577,uu____22578) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22591 = destruct_flex_t t1 wl  in
                  (match uu____22591 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22598;
                    FStar_Syntax_Syntax.pos = uu____22599;
                    FStar_Syntax_Syntax.vars = uu____22600;_},uu____22601),uu____22602)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22639 = destruct_flex_t t1 wl  in
                  (match uu____22639 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22646,FStar_Syntax_Syntax.Tm_uvar uu____22647) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22660,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22661;
                    FStar_Syntax_Syntax.pos = uu____22662;
                    FStar_Syntax_Syntax.vars = uu____22663;_},uu____22664))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22701,FStar_Syntax_Syntax.Tm_arrow uu____22702) ->
                  solve_t' env
                    (let uu___3244_22730 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3244_22730.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3244_22730.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3244_22730.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3244_22730.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3244_22730.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3244_22730.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3244_22730.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3244_22730.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3244_22730.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22731;
                    FStar_Syntax_Syntax.pos = uu____22732;
                    FStar_Syntax_Syntax.vars = uu____22733;_},uu____22734),FStar_Syntax_Syntax.Tm_arrow
                 uu____22735) ->
                  solve_t' env
                    (let uu___3244_22787 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3244_22787.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3244_22787.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3244_22787.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3244_22787.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3244_22787.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3244_22787.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3244_22787.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3244_22787.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3244_22787.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22788,FStar_Syntax_Syntax.Tm_uvar uu____22789) ->
                  let uu____22802 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22802
              | (uu____22803,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22804;
                    FStar_Syntax_Syntax.pos = uu____22805;
                    FStar_Syntax_Syntax.vars = uu____22806;_},uu____22807))
                  ->
                  let uu____22844 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22844
              | (FStar_Syntax_Syntax.Tm_uvar uu____22845,uu____22846) ->
                  let uu____22859 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22859
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22860;
                    FStar_Syntax_Syntax.pos = uu____22861;
                    FStar_Syntax_Syntax.vars = uu____22862;_},uu____22863),uu____22864)
                  ->
                  let uu____22901 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22901
              | (FStar_Syntax_Syntax.Tm_refine uu____22902,uu____22903) ->
                  let t21 =
                    let uu____22911 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22911  in
                  solve_t env
                    (let uu___3279_22937 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3279_22937.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3279_22937.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3279_22937.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3279_22937.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3279_22937.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3279_22937.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3279_22937.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3279_22937.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3279_22937.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22938,FStar_Syntax_Syntax.Tm_refine uu____22939) ->
                  let t11 =
                    let uu____22947 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22947  in
                  solve_t env
                    (let uu___3286_22973 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3286_22973.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3286_22973.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3286_22973.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3286_22973.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3286_22973.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3286_22973.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3286_22973.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3286_22973.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3286_22973.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____23055 =
                    let uu____23056 = guard_of_prob env wl problem t1 t2  in
                    match uu____23056 with
                    | (guard,wl1) ->
                        let uu____23063 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____23063
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23282 = br1  in
                        (match uu____23282 with
                         | (p1,w1,uu____23311) ->
                             let uu____23328 = br2  in
                             (match uu____23328 with
                              | (p2,w2,uu____23351) ->
                                  let uu____23356 =
                                    let uu____23358 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23358  in
                                  if uu____23356
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23385 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23385 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23422 = br2  in
                                         (match uu____23422 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23455 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23455
                                                 in
                                              let uu____23460 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23491,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23512) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23571 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23571 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23460
                                                (fun uu____23643  ->
                                                   match uu____23643 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23680 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23680
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23701
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23701
                                                              then
                                                                let uu____23706
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23708
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23706
                                                                  uu____23708
                                                              else ());
                                                             (let uu____23714
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23714
                                                                (fun
                                                                   uu____23750
                                                                    ->
                                                                   match uu____23750
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
                    | uu____23879 -> FStar_Pervasives_Native.None  in
                  let uu____23920 = solve_branches wl brs1 brs2  in
                  (match uu____23920 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23946 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23946 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23973 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23973 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____24007 =
                                FStar_List.map
                                  (fun uu____24019  ->
                                     match uu____24019 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____24007  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____24028 =
                              let uu____24029 =
                                let uu____24030 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____24030
                                  (let uu___3385_24038 = wl3  in
                                   {
                                     attempting =
                                       (uu___3385_24038.attempting);
                                     wl_deferred =
                                       (uu___3385_24038.wl_deferred);
                                     ctr = (uu___3385_24038.ctr);
                                     defer_ok = (uu___3385_24038.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3385_24038.umax_heuristic_ok);
                                     tcenv = (uu___3385_24038.tcenv);
                                     wl_implicits =
                                       (uu___3385_24038.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3385_24038.repr_subcomp_allowed)
                                   })
                                 in
                              solve env uu____24029  in
                            (match uu____24028 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____24043 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24052 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____24052 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24055,uu____24056) ->
                  let head1 =
                    let uu____24080 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24080
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24126 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24126
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24172 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24172
                    then
                      let uu____24176 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24178 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24180 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24176 uu____24178 uu____24180
                    else ());
                   (let no_free_uvars t =
                      (let uu____24194 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24194) &&
                        (let uu____24198 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24198)
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
                      let uu____24217 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24217 = FStar_Syntax_Util.Equal  in
                    let uu____24218 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24218
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24222 = equal t1 t2  in
                         (if uu____24222
                          then
                            let uu____24225 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24225
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24230 =
                            let uu____24237 = equal t1 t2  in
                            if uu____24237
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24250 = mk_eq2 wl env orig t1 t2  in
                               match uu____24250 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24230 with
                          | (guard,wl1) ->
                              let uu____24271 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24271))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24274,uu____24275) ->
                  let head1 =
                    let uu____24283 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24283
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24329 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24329
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24375 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24375
                    then
                      let uu____24379 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24381 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24383 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24379 uu____24381 uu____24383
                    else ());
                   (let no_free_uvars t =
                      (let uu____24397 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24397) &&
                        (let uu____24401 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24401)
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
                      let uu____24420 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24420 = FStar_Syntax_Util.Equal  in
                    let uu____24421 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24421
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24425 = equal t1 t2  in
                         (if uu____24425
                          then
                            let uu____24428 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24428
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24433 =
                            let uu____24440 = equal t1 t2  in
                            if uu____24440
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24453 = mk_eq2 wl env orig t1 t2  in
                               match uu____24453 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24433 with
                          | (guard,wl1) ->
                              let uu____24474 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24474))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24477,uu____24478) ->
                  let head1 =
                    let uu____24480 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24480
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24526 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24526
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24572 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24572
                    then
                      let uu____24576 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24578 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24580 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24576 uu____24578 uu____24580
                    else ());
                   (let no_free_uvars t =
                      (let uu____24594 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24594) &&
                        (let uu____24598 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24598)
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
                      let uu____24617 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24617 = FStar_Syntax_Util.Equal  in
                    let uu____24618 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24618
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24622 = equal t1 t2  in
                         (if uu____24622
                          then
                            let uu____24625 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24625
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24630 =
                            let uu____24637 = equal t1 t2  in
                            if uu____24637
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24650 = mk_eq2 wl env orig t1 t2  in
                               match uu____24650 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24630 with
                          | (guard,wl1) ->
                              let uu____24671 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24671))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24674,uu____24675) ->
                  let head1 =
                    let uu____24677 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24677
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24723 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24723
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24769 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24769
                    then
                      let uu____24773 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24775 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24777 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24773 uu____24775 uu____24777
                    else ());
                   (let no_free_uvars t =
                      (let uu____24791 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24791) &&
                        (let uu____24795 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24795)
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
                      let uu____24814 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24814 = FStar_Syntax_Util.Equal  in
                    let uu____24815 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24815
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24819 = equal t1 t2  in
                         (if uu____24819
                          then
                            let uu____24822 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24822
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24827 =
                            let uu____24834 = equal t1 t2  in
                            if uu____24834
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24847 = mk_eq2 wl env orig t1 t2  in
                               match uu____24847 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24827 with
                          | (guard,wl1) ->
                              let uu____24868 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24868))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24871,uu____24872) ->
                  let head1 =
                    let uu____24874 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24874
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24920 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24920
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24966 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24966
                    then
                      let uu____24970 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24972 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24974 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24970 uu____24972 uu____24974
                    else ());
                   (let no_free_uvars t =
                      (let uu____24988 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24988) &&
                        (let uu____24992 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24992)
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
                      let uu____25011 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25011 = FStar_Syntax_Util.Equal  in
                    let uu____25012 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25012
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25016 = equal t1 t2  in
                         (if uu____25016
                          then
                            let uu____25019 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25019
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25024 =
                            let uu____25031 = equal t1 t2  in
                            if uu____25031
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25044 = mk_eq2 wl env orig t1 t2  in
                               match uu____25044 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25024 with
                          | (guard,wl1) ->
                              let uu____25065 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25065))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25068,uu____25069) ->
                  let head1 =
                    let uu____25087 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25087
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25133 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25133
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25179 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25179
                    then
                      let uu____25183 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25185 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25187 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25183 uu____25185 uu____25187
                    else ());
                   (let no_free_uvars t =
                      (let uu____25201 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25201) &&
                        (let uu____25205 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25205)
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
                      let uu____25224 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25224 = FStar_Syntax_Util.Equal  in
                    let uu____25225 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25225
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25229 = equal t1 t2  in
                         (if uu____25229
                          then
                            let uu____25232 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25232
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25237 =
                            let uu____25244 = equal t1 t2  in
                            if uu____25244
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25257 = mk_eq2 wl env orig t1 t2  in
                               match uu____25257 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25237 with
                          | (guard,wl1) ->
                              let uu____25278 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25278))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25281,FStar_Syntax_Syntax.Tm_match uu____25282) ->
                  let head1 =
                    let uu____25306 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25306
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25352 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25352
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25398 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25398
                    then
                      let uu____25402 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25404 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25406 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25402 uu____25404 uu____25406
                    else ());
                   (let no_free_uvars t =
                      (let uu____25420 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25420) &&
                        (let uu____25424 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25424)
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
                      let uu____25443 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25443 = FStar_Syntax_Util.Equal  in
                    let uu____25444 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25444
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25448 = equal t1 t2  in
                         (if uu____25448
                          then
                            let uu____25451 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25451
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25456 =
                            let uu____25463 = equal t1 t2  in
                            if uu____25463
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25476 = mk_eq2 wl env orig t1 t2  in
                               match uu____25476 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25456 with
                          | (guard,wl1) ->
                              let uu____25497 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25497))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25500,FStar_Syntax_Syntax.Tm_uinst uu____25501) ->
                  let head1 =
                    let uu____25509 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25509
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25555 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25555
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25601 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25601
                    then
                      let uu____25605 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25607 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25609 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25605 uu____25607 uu____25609
                    else ());
                   (let no_free_uvars t =
                      (let uu____25623 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25623) &&
                        (let uu____25627 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25627)
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
                      let uu____25646 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25646 = FStar_Syntax_Util.Equal  in
                    let uu____25647 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25647
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25651 = equal t1 t2  in
                         (if uu____25651
                          then
                            let uu____25654 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25654
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25659 =
                            let uu____25666 = equal t1 t2  in
                            if uu____25666
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25679 = mk_eq2 wl env orig t1 t2  in
                               match uu____25679 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25659 with
                          | (guard,wl1) ->
                              let uu____25700 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25700))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25703,FStar_Syntax_Syntax.Tm_name uu____25704) ->
                  let head1 =
                    let uu____25706 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25706
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25752 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25752
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25792 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25792
                    then
                      let uu____25796 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25798 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25800 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25796 uu____25798 uu____25800
                    else ());
                   (let no_free_uvars t =
                      (let uu____25814 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25814) &&
                        (let uu____25818 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25818)
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
                      let uu____25837 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25837 = FStar_Syntax_Util.Equal  in
                    let uu____25838 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25838
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25842 = equal t1 t2  in
                         (if uu____25842
                          then
                            let uu____25845 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25845
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25850 =
                            let uu____25857 = equal t1 t2  in
                            if uu____25857
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25870 = mk_eq2 wl env orig t1 t2  in
                               match uu____25870 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25850 with
                          | (guard,wl1) ->
                              let uu____25891 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25891))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25894,FStar_Syntax_Syntax.Tm_constant uu____25895) ->
                  let head1 =
                    let uu____25897 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25897
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25937 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25937
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25977 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25977
                    then
                      let uu____25981 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25983 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25985 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25981 uu____25983 uu____25985
                    else ());
                   (let no_free_uvars t =
                      (let uu____25999 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25999) &&
                        (let uu____26003 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26003)
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
                      let uu____26022 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26022 = FStar_Syntax_Util.Equal  in
                    let uu____26023 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26023
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26027 = equal t1 t2  in
                         (if uu____26027
                          then
                            let uu____26030 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26030
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26035 =
                            let uu____26042 = equal t1 t2  in
                            if uu____26042
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26055 = mk_eq2 wl env orig t1 t2  in
                               match uu____26055 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26035 with
                          | (guard,wl1) ->
                              let uu____26076 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26076))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26079,FStar_Syntax_Syntax.Tm_fvar uu____26080) ->
                  let head1 =
                    let uu____26082 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26082
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26128 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26128
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26174 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26174
                    then
                      let uu____26178 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26180 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26182 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26178 uu____26180 uu____26182
                    else ());
                   (let no_free_uvars t =
                      (let uu____26196 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26196) &&
                        (let uu____26200 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26200)
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
                      let uu____26219 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26219 = FStar_Syntax_Util.Equal  in
                    let uu____26220 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26220
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26224 = equal t1 t2  in
                         (if uu____26224
                          then
                            let uu____26227 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26227
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26232 =
                            let uu____26239 = equal t1 t2  in
                            if uu____26239
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26252 = mk_eq2 wl env orig t1 t2  in
                               match uu____26252 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26232 with
                          | (guard,wl1) ->
                              let uu____26273 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26273))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26276,FStar_Syntax_Syntax.Tm_app uu____26277) ->
                  let head1 =
                    let uu____26295 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26295
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26335 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26335
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26375 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26375
                    then
                      let uu____26379 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26381 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26383 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26379 uu____26381 uu____26383
                    else ());
                   (let no_free_uvars t =
                      (let uu____26397 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26397) &&
                        (let uu____26401 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26401)
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
                      let uu____26420 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26420 = FStar_Syntax_Util.Equal  in
                    let uu____26421 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26421
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26425 = equal t1 t2  in
                         (if uu____26425
                          then
                            let uu____26428 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26428
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26433 =
                            let uu____26440 = equal t1 t2  in
                            if uu____26440
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26453 = mk_eq2 wl env orig t1 t2  in
                               match uu____26453 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26433 with
                          | (guard,wl1) ->
                              let uu____26474 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26474))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26477,FStar_Syntax_Syntax.Tm_let uu____26478) ->
                  let uu____26505 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26505
                  then
                    let uu____26508 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26508
                  else
                    (let uu____26511 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26511 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26514,uu____26515) ->
                  let uu____26529 =
                    let uu____26535 =
                      let uu____26537 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26539 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26541 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26543 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26537 uu____26539 uu____26541 uu____26543
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26535)
                     in
                  FStar_Errors.raise_error uu____26529
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26547,FStar_Syntax_Syntax.Tm_let uu____26548) ->
                  let uu____26562 =
                    let uu____26568 =
                      let uu____26570 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26572 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26574 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26576 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26570 uu____26572 uu____26574 uu____26576
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26568)
                     in
                  FStar_Errors.raise_error uu____26562
                    t1.FStar_Syntax_Syntax.pos
              | uu____26580 ->
                  let uu____26585 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26585 orig))))

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
          (let uu____26651 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26651
           then
             let uu____26656 =
               let uu____26658 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26658  in
             let uu____26659 =
               let uu____26661 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26661  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26656 uu____26659
           else ());
          (let uu____26665 =
             let uu____26667 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26667  in
           if uu____26665
           then
             let uu____26670 =
               mklstr
                 (fun uu____26677  ->
                    let uu____26678 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26680 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26678 uu____26680)
                in
             giveup env uu____26670 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26702 =
                  mklstr
                    (fun uu____26709  ->
                       let uu____26710 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26712 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26710 uu____26712)
                   in
                giveup env uu____26702 orig)
             else
               (let uu____26717 =
                  FStar_List.fold_left2
                    (fun uu____26738  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26738 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26759 =
                                 let uu____26764 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26765 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26764
                                   FStar_TypeChecker_Common.EQ uu____26765
                                   "effect universes"
                                  in
                               (match uu____26759 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26717 with
                | (univ_sub_probs,wl1) ->
                    let uu____26785 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26785 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26793 =
                           FStar_List.fold_right2
                             (fun uu____26830  ->
                                fun uu____26831  ->
                                  fun uu____26832  ->
                                    match (uu____26830, uu____26831,
                                            uu____26832)
                                    with
                                    | ((a1,uu____26876),(a2,uu____26878),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26911 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26911 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26793 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26938 =
                                  let uu____26941 =
                                    let uu____26944 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26944
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26941
                                   in
                                FStar_List.append univ_sub_probs uu____26938
                                 in
                              let guard =
                                let guard =
                                  let uu____26966 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26966  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3537_26975 = wl3  in
                                {
                                  attempting = (uu___3537_26975.attempting);
                                  wl_deferred = (uu___3537_26975.wl_deferred);
                                  ctr = (uu___3537_26975.ctr);
                                  defer_ok = (uu___3537_26975.defer_ok);
                                  smt_ok = (uu___3537_26975.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3537_26975.umax_heuristic_ok);
                                  tcenv = (uu___3537_26975.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3537_26975.repr_subcomp_allowed)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26977 = attempt sub_probs wl5  in
                              solve env uu____26977))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26995 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26995
           then
             let uu____27000 =
               let uu____27002 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27002
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____27004 =
               let uu____27006 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27006
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27000 uu____27004
           else ());
          (let uu____27011 =
             let uu____27016 =
               let uu____27021 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27021
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____27016
               (fun uu____27038  ->
                  match uu____27038 with
                  | (c,g) ->
                      let uu____27049 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____27049, g))
              in
           match uu____27011 with
           | (c12,g_lift) ->
               ((let uu____27053 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____27053
                 then
                   let uu____27058 =
                     let uu____27060 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27060
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____27062 =
                     let uu____27064 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27064
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____27058 uu____27062
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3557_27074 = wl  in
                     {
                       attempting = (uu___3557_27074.attempting);
                       wl_deferred = (uu___3557_27074.wl_deferred);
                       ctr = (uu___3557_27074.ctr);
                       defer_ok = (uu___3557_27074.defer_ok);
                       smt_ok = (uu___3557_27074.smt_ok);
                       umax_heuristic_ok =
                         (uu___3557_27074.umax_heuristic_ok);
                       tcenv = (uu___3557_27074.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits);
                       repr_subcomp_allowed =
                         (uu___3557_27074.repr_subcomp_allowed)
                     }  in
                   let uu____27075 =
                     let rec is_uvar t =
                       let uu____27089 =
                         let uu____27090 = FStar_Syntax_Subst.compress t  in
                         uu____27090.FStar_Syntax_Syntax.n  in
                       match uu____27089 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____27094 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27109) ->
                           is_uvar t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27115) ->
                           is_uvar t1
                       | uu____27140 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27174  ->
                          fun uu____27175  ->
                            fun uu____27176  ->
                              match (uu____27174, uu____27175, uu____27176)
                              with
                              | ((a1,uu____27220),(a2,uu____27222),(is_sub_probs,wl2))
                                  ->
                                  let uu____27255 = is_uvar a1  in
                                  if uu____27255
                                  then
                                    ((let uu____27265 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27265
                                      then
                                        let uu____27270 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27272 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27270 uu____27272
                                      else ());
                                     (let uu____27277 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27277 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____27075 with
                   | (is_sub_probs,wl2) ->
                       let uu____27305 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27305 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27313 =
                              let uu____27318 =
                                let uu____27319 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27319
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27318
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27313 with
                             | (uu____27326,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27337 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27339 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27337 s uu____27339
                                    in
                                 let uu____27342 =
                                   let uu____27371 =
                                     let uu____27372 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27372.FStar_Syntax_Syntax.n  in
                                   match uu____27371 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27432 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27432 with
                                        | (bs',c3) ->
                                            let a = FStar_List.hd bs'  in
                                            let bs1 = FStar_List.tail bs'  in
                                            let uu____27495 =
                                              let uu____27514 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27514
                                                (fun uu____27618  ->
                                                   match uu____27618 with
                                                   | (l1,l2) ->
                                                       let uu____27691 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27691))
                                               in
                                            (match uu____27495 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27796 ->
                                       let uu____27797 =
                                         let uu____27803 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27803)
                                          in
                                       FStar_Errors.raise_error uu____27797 r
                                    in
                                 (match uu____27342 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27879 =
                                        let uu____27886 =
                                          let uu____27887 =
                                            let uu____27888 =
                                              let uu____27895 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27895,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27888
                                             in
                                          [uu____27887]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27886
                                          (fun b  ->
                                             let uu____27911 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27913 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27915 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27911 uu____27913
                                               uu____27915) r
                                         in
                                      (match uu____27879 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27925 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27925
                                             then
                                               let uu____27930 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27939 =
                                                          let uu____27941 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27941
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27939) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27930
                                             else ());
                                            (let wl4 =
                                               let uu___3629_27949 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3629_27949.attempting);
                                                 wl_deferred =
                                                   (uu___3629_27949.wl_deferred);
                                                 ctr = (uu___3629_27949.ctr);
                                                 defer_ok =
                                                   (uu___3629_27949.defer_ok);
                                                 smt_ok =
                                                   (uu___3629_27949.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3629_27949.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3629_27949.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits);
                                                 repr_subcomp_allowed =
                                                   (uu___3629_27949.repr_subcomp_allowed)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27974 =
                                                        let uu____27981 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27981, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27974) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27998 =
                                               let f_sort_is =
                                                 let uu____28008 =
                                                   let uu____28009 =
                                                     let uu____28012 =
                                                       let uu____28013 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____28013.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____28012
                                                      in
                                                   uu____28009.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____28008 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____28024,uu____28025::is)
                                                     ->
                                                     let uu____28067 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____28067
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28100 ->
                                                     let uu____28101 =
                                                       let uu____28107 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28107)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28101 r
                                                  in
                                               let uu____28113 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28148  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28148
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28169 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28169
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28113
                                                in
                                             match uu____27998 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28194 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28194
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28195 =
                                                   let g_sort_is =
                                                     let uu____28205 =
                                                       let uu____28206 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28206.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28205 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28211,uu____28212::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28272 ->
                                                         let uu____28273 =
                                                           let uu____28279 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28279)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28273 r
                                                      in
                                                   let uu____28285 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28320  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28320
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28341
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28341
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28285
                                                    in
                                                 (match uu____28195 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28368 =
                                                          let uu____28373 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28374 =
                                                            let uu____28375 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28375
                                                             in
                                                          (uu____28373,
                                                            uu____28374)
                                                           in
                                                        match uu____28368
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28403 =
                                                          let uu____28406 =
                                                            let uu____28409 =
                                                              let uu____28412
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28412
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28409
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28406
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28403
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28436 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28436
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
                                                        let uu____28447 =
                                                          let uu____28450 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun uu____28453 
                                                               ->
                                                               FStar_Pervasives_Native.Some
                                                                 uu____28453)
                                                            uu____28450
                                                           in
                                                        solve_prob orig
                                                          uu____28447 [] wl6
                                                         in
                                                      let uu____28454 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28454))))))))))
           in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env  in
           let lift_c1 uu____28482 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____28484 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ
                      in
                   [uu____28484]
               | x -> x  in
             let c12 =
               let uu___3697_28487 = c11  in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3697_28487.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3697_28487.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3697_28487.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3697_28487.FStar_Syntax_Syntax.flags)
               }  in
             let uu____28488 =
               let uu____28493 =
                 FStar_All.pipe_right
                   (let uu___3700_28495 = c12  in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3700_28495.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3700_28495.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3700_28495.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3700_28495.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____28493
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____28488
               (fun uu____28509  ->
                  match uu____28509 with
                  | (c,g) ->
                      let uu____28516 =
                        let uu____28518 = FStar_TypeChecker_Env.is_trivial g
                           in
                        Prims.op_Negation uu____28518  in
                      if uu____28516
                      then
                        let uu____28521 =
                          let uu____28527 =
                            let uu____28529 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name
                               in
                            let uu____28531 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name
                               in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____28529 uu____28531
                             in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____28527)
                           in
                        FStar_Errors.raise_error uu____28521 r
                      else FStar_Syntax_Util.comp_to_comp_typ c)
              in
           let uu____28537 =
             FStar_TypeChecker_Env.is_layered_effect env
               c21.FStar_Syntax_Syntax.effect_name
              in
           if uu____28537
           then solve_layered_sub c11 edge c21
           else
             (let uu____28542 =
                ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                   (let uu____28545 =
                      FStar_Ident.lid_equals
                        c11.FStar_Syntax_Syntax.effect_name
                        c21.FStar_Syntax_Syntax.effect_name
                       in
                    Prims.op_Negation uu____28545))
                  &&
                  (FStar_TypeChecker_Env.is_reifiable_effect env
                     c21.FStar_Syntax_Syntax.effect_name)
                 in
              if uu____28542
              then
                let uu____28548 =
                  mklstr
                    (fun uu____28555  ->
                       let uu____28556 =
                         FStar_Ident.string_of_lid
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____28558 =
                         FStar_Ident.string_of_lid
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Cannot lift from %s to %s, it needs a lift\n"
                         uu____28556 uu____28558)
                   in
                giveup env uu____28548 orig
              else
                (let is_null_wp_2 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___29_28569  ->
                           match uu___29_28569 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | FStar_Syntax_Syntax.MLEFFECT  -> true
                           | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                           | uu____28574 -> false))
                    in
                 let uu____28576 =
                   match ((c11.FStar_Syntax_Syntax.effect_args),
                           (c21.FStar_Syntax_Syntax.effect_args))
                   with
                   | ((wp1,uu____28606)::uu____28607,(wp2,uu____28609)::uu____28610)
                       -> (wp1, wp2)
                   | uu____28683 ->
                       let uu____28708 =
                         let uu____28714 =
                           let uu____28716 =
                             FStar_Syntax_Print.lid_to_string
                               c11.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28718 =
                             FStar_Syntax_Print.lid_to_string
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Got effects %s and %s, expected normalized effects"
                             uu____28716 uu____28718
                            in
                         (FStar_Errors.Fatal_ExpectNormalizedEffect,
                           uu____28714)
                          in
                       FStar_Errors.raise_error uu____28708
                         env.FStar_TypeChecker_Env.range
                    in
                 match uu____28576 with
                 | (wpc1,wpc2) ->
                     let uu____28728 = FStar_Util.physical_equality wpc1 wpc2
                        in
                     if uu____28728
                     then
                       let uu____28731 =
                         problem_using_guard orig
                           c11.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____28731 wl
                     else
                       (let uu____28735 =
                          let uu____28742 =
                            FStar_TypeChecker_Env.effect_decl_opt env
                              c21.FStar_Syntax_Syntax.effect_name
                             in
                          FStar_Util.must uu____28742  in
                        match uu____28735 with
                        | (c2_decl,qualifiers) ->
                            let uu____28763 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            if uu____28763
                            then
                              let c1_repr =
                                let uu____28770 =
                                  let uu____28771 =
                                    let uu____28772 = lift_c1 ()  in
                                    FStar_Syntax_Syntax.mk_Comp uu____28772
                                     in
                                  let uu____28773 =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  FStar_TypeChecker_Env.reify_comp env
                                    uu____28771 uu____28773
                                   in
                                norm_with_steps
                                  "FStar.TypeChecker.Rel.norm_with_steps.4"
                                  [FStar_TypeChecker_Env.UnfoldUntil
                                     FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Env.Weak;
                                  FStar_TypeChecker_Env.HNF] env uu____28770
                                 in
                              let c2_repr =
                                let uu____28776 =
                                  let uu____28777 =
                                    FStar_Syntax_Syntax.mk_Comp c21  in
                                  let uu____28778 =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  FStar_TypeChecker_Env.reify_comp env
                                    uu____28777 uu____28778
                                   in
                                norm_with_steps
                                  "FStar.TypeChecker.Rel.norm_with_steps.5"
                                  [FStar_TypeChecker_Env.UnfoldUntil
                                     FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Env.Weak;
                                  FStar_TypeChecker_Env.HNF] env uu____28776
                                 in
                              let uu____28780 =
                                let uu____28785 =
                                  let uu____28787 =
                                    FStar_Syntax_Print.term_to_string c1_repr
                                     in
                                  let uu____28789 =
                                    FStar_Syntax_Print.term_to_string c2_repr
                                     in
                                  FStar_Util.format2
                                    "sub effect repr: %s <: %s" uu____28787
                                    uu____28789
                                   in
                                sub_prob wl c1_repr
                                  problem.FStar_TypeChecker_Common.relation
                                  c2_repr uu____28785
                                 in
                              (match uu____28780 with
                               | (prob,wl1) ->
                                   let wl2 =
                                     solve_prob orig
                                       (FStar_Pervasives_Native.Some
                                          (p_guard prob)) [] wl1
                                      in
                                   let uu____28795 = attempt [prob] wl2  in
                                   solve env uu____28795)
                            else
                              (let g =
                                 if env.FStar_TypeChecker_Env.lax
                                 then FStar_Syntax_Util.t_true
                                 else
                                   (let wpc1_2 =
                                      let uu____28815 = lift_c1 ()  in
                                      FStar_All.pipe_right uu____28815
                                        (fun ct  ->
                                           FStar_List.hd
                                             ct.FStar_Syntax_Syntax.effect_args)
                                       in
                                    if is_null_wp_2
                                    then
                                      ((let uu____28838 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other "Rel")
                                           in
                                        if uu____28838
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
                                          let uu____28848 =
                                            FStar_All.pipe_right c2_decl
                                              FStar_Syntax_Util.get_wp_trivial_combinator
                                             in
                                          match uu____28848 with
                                          | FStar_Pervasives_Native.None  ->
                                              failwith
                                                "Rel doesn't yet handle undefined trivial combinator in an effect"
                                          | FStar_Pervasives_Native.Some t ->
                                              t
                                           in
                                        let uu____28855 =
                                          let uu____28862 =
                                            let uu____28863 =
                                              let uu____28880 =
                                                FStar_TypeChecker_Env.inst_effect_fun_with
                                                  [c1_univ] env c2_decl
                                                  trivial
                                                 in
                                              let uu____28883 =
                                                let uu____28894 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                   in
                                                [uu____28894; wpc1_2]  in
                                              (uu____28880, uu____28883)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____28863
                                             in
                                          FStar_Syntax_Syntax.mk uu____28862
                                           in
                                        uu____28855
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
                                       let uu____28943 =
                                         let uu____28950 =
                                           let uu____28951 =
                                             let uu____28968 =
                                               FStar_TypeChecker_Env.inst_effect_fun_with
                                                 [c2_univ] env c2_decl
                                                 stronger
                                                in
                                             let uu____28971 =
                                               let uu____28982 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   c21.FStar_Syntax_Syntax.result_typ
                                                  in
                                               let uu____28991 =
                                                 let uu____29002 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     wpc2
                                                    in
                                                 [uu____29002; wpc1_2]  in
                                               uu____28982 :: uu____28991  in
                                             (uu____28968, uu____28971)  in
                                           FStar_Syntax_Syntax.Tm_app
                                             uu____28951
                                            in
                                         FStar_Syntax_Syntax.mk uu____28950
                                          in
                                       uu____28943
                                         FStar_Pervasives_Native.None r))
                                  in
                               (let uu____29056 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____29056
                                then
                                  let uu____29061 =
                                    let uu____29063 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Iota;
                                        FStar_TypeChecker_Env.Eager_unfolding;
                                        FStar_TypeChecker_Env.Primops;
                                        FStar_TypeChecker_Env.Simplify] env g
                                       in
                                    FStar_Syntax_Print.term_to_string
                                      uu____29063
                                     in
                                  FStar_Util.print1
                                    "WP guard (simplifed) is (%s)\n"
                                    uu____29061
                                else ());
                               (let uu____29067 =
                                  sub_prob wl
                                    c11.FStar_Syntax_Syntax.result_typ
                                    problem.FStar_TypeChecker_Common.relation
                                    c21.FStar_Syntax_Syntax.result_typ
                                    "result type"
                                   in
                                match uu____29067 with
                                | (base_prob,wl1) ->
                                    let wl2 =
                                      let uu____29076 =
                                        let uu____29079 =
                                          FStar_Syntax_Util.mk_conj
                                            (p_guard base_prob) g
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____29082  ->
                                             FStar_Pervasives_Native.Some
                                               uu____29082) uu____29079
                                         in
                                      solve_prob orig uu____29076 [] wl1  in
                                    let uu____29083 = attempt [base_prob] wl2
                                       in
                                    solve env uu____29083))))))
           in
        let uu____29084 = FStar_Util.physical_equality c1 c2  in
        if uu____29084
        then
          let uu____29087 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____29087
        else
          ((let uu____29091 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____29091
            then
              let uu____29096 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____29098 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29096
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29098
            else ());
           (let uu____29103 =
              let uu____29112 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29115 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29112, uu____29115)  in
            match uu____29103 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29133),FStar_Syntax_Syntax.Total
                    (t2,uu____29135)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29152 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29152 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29154,FStar_Syntax_Syntax.Total uu____29155) ->
                     let uu____29172 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29172 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29176),FStar_Syntax_Syntax.Total
                    (t2,uu____29178)) ->
                     let uu____29195 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29195 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29198),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29200)) ->
                     let uu____29217 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29217 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29220),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29222)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29239 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29239 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29242),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29244)) ->
                     let uu____29261 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29261 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29264,FStar_Syntax_Syntax.Comp uu____29265) ->
                     let uu____29274 =
                       let uu___3825_29277 = problem  in
                       let uu____29280 =
                         let uu____29281 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29281
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3825_29277.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29280;
                         FStar_TypeChecker_Common.relation =
                           (uu___3825_29277.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3825_29277.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3825_29277.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3825_29277.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3825_29277.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3825_29277.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3825_29277.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3825_29277.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29274 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29282,FStar_Syntax_Syntax.Comp uu____29283) ->
                     let uu____29292 =
                       let uu___3825_29295 = problem  in
                       let uu____29298 =
                         let uu____29299 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29299
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3825_29295.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29298;
                         FStar_TypeChecker_Common.relation =
                           (uu___3825_29295.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3825_29295.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3825_29295.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3825_29295.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3825_29295.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3825_29295.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3825_29295.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3825_29295.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29292 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29300,FStar_Syntax_Syntax.GTotal uu____29301) ->
                     let uu____29310 =
                       let uu___3837_29313 = problem  in
                       let uu____29316 =
                         let uu____29317 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29317
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3837_29313.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3837_29313.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3837_29313.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29316;
                         FStar_TypeChecker_Common.element =
                           (uu___3837_29313.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3837_29313.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3837_29313.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3837_29313.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3837_29313.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3837_29313.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29310 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29318,FStar_Syntax_Syntax.Total uu____29319) ->
                     let uu____29328 =
                       let uu___3837_29331 = problem  in
                       let uu____29334 =
                         let uu____29335 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29335
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3837_29331.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3837_29331.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3837_29331.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29334;
                         FStar_TypeChecker_Common.element =
                           (uu___3837_29331.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3837_29331.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3837_29331.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3837_29331.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3837_29331.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3837_29331.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29328 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29336,FStar_Syntax_Syntax.Comp uu____29337) ->
                     let uu____29338 =
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
                     if uu____29338
                     then
                       let uu____29341 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29341 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29348 =
                            let uu____29353 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29353
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29362 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29363 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29362, uu____29363))
                             in
                          match uu____29348 with
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
                           (let uu____29371 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29371
                            then
                              let uu____29376 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name
                                 in
                              let uu____29378 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____29376 uu____29378
                            else ());
                           (let uu____29383 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29383 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29386 =
                                  mklstr
                                    (fun uu____29393  ->
                                       let uu____29394 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29396 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29394 uu____29396)
                                   in
                                giveup env uu____29386 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29407 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29407 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29457 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29457 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29482 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29513  ->
                match uu____29513 with
                | (u1,u2) ->
                    let uu____29521 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29523 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29521 uu____29523))
         in
      FStar_All.pipe_right uu____29482 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29560,[])) when
          let uu____29587 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29587 -> "{}"
      | uu____29590 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29617 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29617
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29629 =
              FStar_List.map
                (fun uu____29642  ->
                   match uu____29642 with
                   | (uu____29649,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29629 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29660 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29660 imps
  
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
                  let uu____29717 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29717
                  then
                    let uu____29725 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29727 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29725
                      (rel_to_string rel) uu____29727
                  else "TOP"  in
                let uu____29733 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29733 with
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
              let uu____29793 =
                let uu____29796 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun uu____29799  ->
                     FStar_Pervasives_Native.Some uu____29799) uu____29796
                 in
              FStar_Syntax_Syntax.new_bv uu____29793 t1  in
            let uu____29800 =
              let uu____29805 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29805
               in
            match uu____29800 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29863 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29863
         then
           let uu____29868 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29868
         else ());
        (let uu____29875 =
           FStar_Util.record_time (fun uu____29882  -> solve env probs)  in
         match uu____29875 with
         | (sol,ms) ->
             ((let uu____29894 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29894
               then
                 let uu____29899 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29899
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29912 =
                     FStar_Util.record_time
                       (fun uu____29919  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29912 with
                    | ((),ms1) ->
                        ((let uu____29930 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29930
                          then
                            let uu____29935 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29935
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29947 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29947
                     then
                       let uu____29954 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29954
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
          ((let uu____29980 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29980
            then
              let uu____29985 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29985
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29993 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29993
             then
               let uu____29998 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29998
             else ());
            (let f2 =
               let uu____30004 =
                 let uu____30005 = FStar_Syntax_Util.unmeta f1  in
                 uu____30005.FStar_Syntax_Syntax.n  in
               match uu____30004 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30009 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3954_30010 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3954_30010.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3954_30010.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3954_30010.FStar_TypeChecker_Common.implicits)
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
            let uu____30053 =
              let uu____30054 =
                let uu____30055 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____30056  ->
                       FStar_TypeChecker_Common.NonTrivial uu____30056)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30055;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____30054  in
            FStar_All.pipe_left
              (fun uu____30063  -> FStar_Pervasives_Native.Some uu____30063)
              uu____30053
  
let with_guard_no_simp :
  'uuuuuu30073 .
    'uuuuuu30073 ->
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
            let uu____30113 =
              let uu____30114 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____30115  ->
                     FStar_TypeChecker_Common.NonTrivial uu____30115)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30114;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30113
  
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
          (let uu____30148 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30148
           then
             let uu____30153 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30155 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30153
               uu____30155
           else ());
          (let uu____30160 =
             let uu____30165 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30165
              in
           match uu____30160 with
           | (prob,wl) ->
               let g =
                 let uu____30173 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30181  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30173  in
               ((let uu____30199 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30199
                 then
                   let uu____30204 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30204
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
        let uu____30225 = try_teq true env t1 t2  in
        match uu____30225 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30230 = FStar_TypeChecker_Env.get_range env  in
              let uu____30231 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30230 uu____30231);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30239 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30239
              then
                let uu____30244 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30246 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30248 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30244
                  uu____30246 uu____30248
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
        (let uu____30272 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30272
         then
           let uu____30277 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30279 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30277
             uu____30279
         else ());
        (let uu____30284 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30284 with
         | (prob,x,wl) ->
             let g =
               let uu____30299 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30308  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30299  in
             ((let uu____30326 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30326
               then
                 let uu____30331 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30331
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30339 =
                     let uu____30340 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30340 g1  in
                   FStar_Pervasives_Native.Some uu____30339)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30362 = FStar_TypeChecker_Env.get_range env  in
          let uu____30363 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30362 uu____30363
  
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
        (let uu____30392 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30392
         then
           let uu____30397 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30399 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30397 uu____30399
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30410 =
           let uu____30417 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30417 "sub_comp"
            in
         match uu____30410 with
         | (prob,wl) ->
             let wl1 =
               let uu___4025_30428 = wl  in
               {
                 attempting = (uu___4025_30428.attempting);
                 wl_deferred = (uu___4025_30428.wl_deferred);
                 ctr = (uu___4025_30428.ctr);
                 defer_ok = (uu___4025_30428.defer_ok);
                 smt_ok = (uu___4025_30428.smt_ok);
                 umax_heuristic_ok = (uu___4025_30428.umax_heuristic_ok);
                 tcenv = (uu___4025_30428.tcenv);
                 wl_implicits = (uu___4025_30428.wl_implicits);
                 repr_subcomp_allowed = true
               }  in
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30433 =
                 FStar_Util.record_time
                   (fun uu____30445  ->
                      let uu____30446 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____30455  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30446)
                  in
               match uu____30433 with
               | (r,ms) ->
                   ((let uu____30483 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30483
                     then
                       let uu____30488 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30490 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30492 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30488 uu____30490
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30492
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
      fun uu____30530  ->
        match uu____30530 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30573 =
                 let uu____30579 =
                   let uu____30581 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30583 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30581 uu____30583
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30579)  in
               let uu____30587 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30573 uu____30587)
               in
            let equiv v v' =
              let uu____30600 =
                let uu____30605 = FStar_Syntax_Subst.compress_univ v  in
                let uu____30606 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30605, uu____30606)  in
              match uu____30600 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30630 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v  ->
                      let uu____30661 = FStar_Syntax_Subst.compress_univ v
                         in
                      match uu____30661 with
                      | FStar_Syntax_Syntax.U_unif uu____30668 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30699  ->
                                    match uu____30699 with
                                    | (u,v') ->
                                        let uu____30708 = equiv v v'  in
                                        if uu____30708
                                        then
                                          let uu____30713 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____30713 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v)]
                      | uu____30734 -> []))
               in
            let uu____30739 =
              let wl =
                let uu___4068_30743 = empty_worklist env  in
                {
                  attempting = (uu___4068_30743.attempting);
                  wl_deferred = (uu___4068_30743.wl_deferred);
                  ctr = (uu___4068_30743.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4068_30743.smt_ok);
                  umax_heuristic_ok = (uu___4068_30743.umax_heuristic_ok);
                  tcenv = (uu___4068_30743.tcenv);
                  wl_implicits = (uu___4068_30743.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4068_30743.repr_subcomp_allowed)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30762  ->
                      match uu____30762 with
                      | (lb,v) ->
                          let uu____30769 =
                            solve_universe_eq (~- Prims.int_one) wl lb v  in
                          (match uu____30769 with
                           | USolved wl1 -> ()
                           | uu____30772 -> fail lb v)))
               in
            let rec check_ineq uu____30783 =
              match uu____30783 with
              | (u,v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v  in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30795) -> true
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
                      uu____30823,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30825,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30838) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v1)))
                   | (uu____30846,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v2  -> check_ineq (u1, v2)))
                   | uu____30855 -> false)
               in
            let uu____30861 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30878  ->
                      match uu____30878 with
                      | (u,v) ->
                          let uu____30886 = check_ineq (u, v)  in
                          if uu____30886
                          then true
                          else
                            ((let uu____30894 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30894
                              then
                                let uu____30899 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30901 =
                                  FStar_Syntax_Print.univ_to_string v  in
                                FStar_Util.print2 "%s </= %s" uu____30899
                                  uu____30901
                              else ());
                             false)))
               in
            if uu____30861
            then ()
            else
              ((let uu____30911 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30911
                then
                  ((let uu____30917 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30917);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30929 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30929))
                else ());
               (let uu____30942 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30942))
  
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
          let fail uu____31022 =
            match uu____31022 with
            | (d,s) ->
                let msg = explain env d s  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d)
             in
          let wl =
            let uu___4146_31045 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
            {
              attempting = (uu___4146_31045.attempting);
              wl_deferred = (uu___4146_31045.wl_deferred);
              ctr = (uu___4146_31045.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4146_31045.umax_heuristic_ok);
              tcenv = (uu___4146_31045.tcenv);
              wl_implicits = (uu___4146_31045.wl_implicits);
              repr_subcomp_allowed = (uu___4146_31045.repr_subcomp_allowed)
            }  in
          (let uu____31048 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____31048
           then
             let uu____31053 = FStar_Util.string_of_bool defer_ok  in
             let uu____31055 = wl_to_string wl  in
             let uu____31057 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits)
                in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____31053 uu____31055 uu____31057
           else ());
          (let g1 =
             let uu____31063 = solve_and_commit env wl fail  in
             match uu____31063 with
             | FStar_Pervasives_Native.Some
                 (uu____31070::uu____31071,uu____31072) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred,imps) ->
                 let uu___4161_31101 = g  in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4161_31101.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4161_31101.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____31102 ->
                 failwith "Impossible: should have raised a failure already"
              in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let uu___4166_31111 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4166_31111.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred =
                (uu___4166_31111.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs = ([], []);
              FStar_TypeChecker_Common.implicits =
                (uu___4166_31111.FStar_TypeChecker_Common.implicits)
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
            let uu___4181_31208 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4181_31208.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4181_31208.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4181_31208.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____31209 =
            let uu____31211 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____31211  in
          if uu____31209
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug
                  then
                    (let uu____31223 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____31224 =
                       let uu____31226 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____31226
                        in
                     FStar_Errors.diag uu____31223 uu____31224)
                  else ();
                  (let vc1 =
                     let uu____31232 =
                       let uu____31236 =
                         let uu____31238 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____31238  in
                       FStar_Pervasives_Native.Some uu____31236  in
                     FStar_Profiling.profile
                       (fun uu____31241  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____31232 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug
                   then
                     (let uu____31245 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31246 =
                        let uu____31248 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31248
                         in
                      FStar_Errors.diag uu____31245 uu____31246)
                   else ();
                   (let uu____31254 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31254
                      "discharge_guard'" env vc1);
                   (let uu____31256 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31256 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug
                           then
                             (let uu____31265 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31266 =
                                let uu____31268 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31268
                                 in
                              FStar_Errors.diag uu____31265 uu____31266)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug
                           then
                             (let uu____31278 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31279 =
                                let uu____31281 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31281
                                 in
                              FStar_Errors.diag uu____31278 uu____31279)
                           else ();
                           (let vcs =
                              let uu____31295 = FStar_Options.use_tactics ()
                                 in
                              if uu____31295
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31317  ->
                                     (let uu____31319 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        (fun uu____31321  -> ()) uu____31319);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31364  ->
                                              match uu____31364 with
                                              | (env1,goal,opts) ->
                                                  let uu____31380 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31380, opts)))))
                              else
                                (let uu____31384 =
                                   let uu____31391 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31391)  in
                                 [uu____31384])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31424  ->
                                    match uu____31424 with
                                    | (env1,goal,opts) ->
                                        let uu____31434 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31434 with
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
                                                (let uu____31445 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31446 =
                                                   let uu____31448 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31450 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31448 uu____31450
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31445 uu____31446)
                                              else ();
                                              if debug
                                              then
                                                (let uu____31457 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31458 =
                                                   let uu____31460 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31460
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31457 uu____31458)
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
      let uu____31478 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31478 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31487 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31487
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31501 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31501 with
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
        let uu____31531 = try_teq false env t1 t2  in
        match uu____31531 with
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
            let uu____31575 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31575 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31588 ->
                     let uu____31601 =
                       let uu____31602 = FStar_Syntax_Subst.compress r  in
                       uu____31602.FStar_Syntax_Syntax.n  in
                     (match uu____31601 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31607) ->
                          unresolved ctx_u'
                      | uu____31624 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31648 = acc  in
            match uu____31648 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd::tl ->
                     let uu____31667 = hd  in
                     (match uu____31667 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl
                          else
                            (let uu____31678 = unresolved ctx_u  in
                             if uu____31678
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd :: out), changed) tl
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31702 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31702
                                     then
                                       let uu____31706 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31706
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31715 = teq_nosmt env1 t tm
                                          in
                                       match uu____31715 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4294_31725 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4294_31725.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4294_31725.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4294_31725.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4294_31725.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4294_31725.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4294_31725.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4294_31725.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd1 =
                                       let uu___4297_31733 = hd  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4297_31733.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4297_31733.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4297_31733.FStar_TypeChecker_Common.imp_range)
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
                                    let uu___4301_31744 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4301_31744.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4301_31744.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4301_31744.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4301_31744.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4301_31744.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4301_31744.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4301_31744.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4301_31744.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4301_31744.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4301_31744.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4301_31744.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4301_31744.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4301_31744.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4301_31744.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4301_31744.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4301_31744.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4301_31744.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4301_31744.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4301_31744.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4301_31744.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4301_31744.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4301_31744.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4301_31744.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4301_31744.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4301_31744.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4301_31744.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4301_31744.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4301_31744.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4301_31744.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4301_31744.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4301_31744.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4301_31744.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4301_31744.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4301_31744.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4301_31744.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4301_31744.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4301_31744.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4301_31744.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4301_31744.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4301_31744.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4301_31744.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4301_31744.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4301_31744.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4301_31744.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4301_31744.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4306_31749 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4306_31749.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4306_31749.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4306_31749.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4306_31749.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4306_31749.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4306_31749.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4306_31749.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4306_31749.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4306_31749.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4306_31749.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4306_31749.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4306_31749.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4306_31749.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4306_31749.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4306_31749.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4306_31749.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4306_31749.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4306_31749.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4306_31749.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4306_31749.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4306_31749.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4306_31749.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4306_31749.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4306_31749.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4306_31749.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4306_31749.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4306_31749.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4306_31749.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4306_31749.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4306_31749.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4306_31749.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4306_31749.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4306_31749.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4306_31749.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4306_31749.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4306_31749.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4306_31749.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4306_31749.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4306_31749.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4306_31749.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4306_31749.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4306_31749.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4306_31749.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4306_31749.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4306_31749.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31754 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31754
                                   then
                                     let uu____31759 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31761 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31763 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31765 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31759 uu____31761 uu____31763
                                       reason uu____31765
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4312_31772  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31779 =
                                             let uu____31789 =
                                               let uu____31797 =
                                                 let uu____31799 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31801 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31803 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31799 uu____31801
                                                   uu____31803
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31797, r)
                                                in
                                             [uu____31789]  in
                                           FStar_Errors.add_errors
                                             uu____31779);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31822 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31833  ->
                                               let uu____31834 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31836 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31838 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31834 uu____31836
                                                 reason uu____31838)) env2 g1
                                         true
                                        in
                                     match uu____31822 with
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
          let uu___4324_31846 = g  in
          let uu____31847 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4324_31846.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4324_31846.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4324_31846.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31847
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
        let uu____31887 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31887 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31888 = discharge_guard env g1  in
          FStar_All.pipe_left (fun uu____31889  -> ()) uu____31888
      | imp::uu____31891 ->
          let uu____31894 =
            let uu____31900 =
              let uu____31902 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31904 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31902 uu____31904
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31900)
             in
          FStar_Errors.raise_error uu____31894
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31924 = teq env t1 t2  in
        force_trivial_guard env uu____31924
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31943 = teq_nosmt env t1 t2  in
        match uu____31943 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4349_31962 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4349_31962.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4349_31962.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4349_31962.FStar_TypeChecker_Common.implicits)
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
        (let uu____31998 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31998
         then
           let uu____32003 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32005 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____32003
             uu____32005
         else ());
        (let uu____32010 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32010 with
         | (prob,x,wl) ->
             let g =
               let uu____32029 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____32038  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32029  in
             ((let uu____32056 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____32056
               then
                 let uu____32061 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____32063 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____32065 =
                   let uu____32067 = FStar_Util.must g  in
                   guard_to_string env uu____32067  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____32061 uu____32063 uu____32065
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
        let uu____32104 = check_subtyping env t1 t2  in
        match uu____32104 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32123 =
              let uu____32124 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____32124 g  in
            FStar_Pervasives_Native.Some uu____32123
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32143 = check_subtyping env t1 t2  in
        match uu____32143 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32162 =
              let uu____32163 =
                let uu____32164 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____32164]  in
              FStar_TypeChecker_Env.close_guard env uu____32163 g  in
            FStar_Pervasives_Native.Some uu____32162
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32202 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32202
         then
           let uu____32207 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32209 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32207
             uu____32209
         else ());
        (let uu____32214 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32214 with
         | (prob,x,wl) ->
             let g =
               let uu____32229 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32238  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32229  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32259 =
                      let uu____32260 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32260]  in
                    FStar_TypeChecker_Env.close_guard env uu____32259 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32301 = subtype_nosmt env t1 t2  in
        match uu____32301 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  