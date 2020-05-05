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
                          (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange))) r
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
                              let uu____2663 =
                                let uu____2672 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.as_arg uu____2672
                                 in
                              [uu____2663]  in
                            FStar_Syntax_Syntax.mk_Tm_app lg uu____2662 loc
                         in
                      let prob =
                        let uu____2700 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2700;
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
                let uu____2748 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2748;
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
  'uuuuuu2763 .
    worklist ->
      'uuuuuu2763 FStar_TypeChecker_Common.problem ->
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
              let uu____2796 =
                let uu____2799 =
                  let uu____2800 =
                    let uu____2807 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2807)  in
                  FStar_Syntax_Syntax.NT uu____2800  in
                [uu____2799]  in
              FStar_Syntax_Subst.subst uu____2796 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2829 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2829
        then
          let uu____2837 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2840 = prob_to_string env d  in
          let uu____2842 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____2849 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2837 uu____2840 uu____2842 uu____2849
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2861 -> failwith "impossible"  in
           let uu____2864 =
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
           match uu____2864 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2907  ->
            match uu___15_2907 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2921 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2925 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2925 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2956  ->
           match uu___16_2956 with
           | UNIV uu____2959 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2966 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2966
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
        (fun uu___17_2994  ->
           match uu___17_2994 with
           | UNIV (u',t) ->
               let uu____2999 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2999
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____3006 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3018 =
        let uu____3019 =
          let uu____3020 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____3020
           in
        FStar_Syntax_Subst.compress uu____3019  in
      FStar_All.pipe_right uu____3018 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3032 =
        let uu____3033 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____3033  in
      FStar_All.pipe_right uu____3032 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3045 =
        let uu____3049 =
          let uu____3051 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3051  in
        FStar_Pervasives_Native.Some uu____3049  in
      FStar_Profiling.profile (fun uu____3054  -> sn' env t) uu____3045
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
          let uu____3079 =
            let uu____3083 =
              let uu____3085 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3085  in
            FStar_Pervasives_Native.Some uu____3083  in
          FStar_Profiling.profile
            (fun uu____3088  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3079
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3096 = FStar_Syntax_Util.head_and_args t  in
    match uu____3096 with
    | (h,uu____3115) ->
        let uu____3140 =
          let uu____3141 = FStar_Syntax_Subst.compress h  in
          uu____3141.FStar_Syntax_Syntax.n  in
        (match uu____3140 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3146 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3159 =
        let uu____3163 =
          let uu____3165 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3165  in
        FStar_Pervasives_Native.Some uu____3163  in
      FStar_Profiling.profile
        (fun uu____3170  ->
           let uu____3171 = should_strongly_reduce t  in
           if uu____3171
           then
             let uu____3174 =
               let uu____3175 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3175  in
             FStar_All.pipe_right uu____3174 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3159 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'uuuuuu3186 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'uuuuuu3186) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu3186)
  =
  fun env  ->
    fun t  ->
      let uu____3209 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3209, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3261  ->
              match uu____3261 with
              | (x,imp) ->
                  let uu____3280 =
                    let uu___466_3281 = x  in
                    let uu____3282 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___466_3281.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___466_3281.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3282
                    }  in
                  (uu____3280, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3306 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3306
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3310 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3310
        | uu____3313 -> u2  in
      let uu____3314 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3314
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3331 =
          let uu____3335 =
            let uu____3337 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3337  in
          FStar_Pervasives_Native.Some uu____3335  in
        FStar_Profiling.profile
          (fun uu____3340  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3331 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
                (let uu____3462 = norm_refinement env t12  in
                 match uu____3462 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3477;
                     FStar_Syntax_Syntax.vars = uu____3478;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3502 =
                       let uu____3504 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3506 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3504 uu____3506
                        in
                     failwith uu____3502)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3522 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm uu____3522
          | FStar_Syntax_Syntax.Tm_uinst uu____3523 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3560 =
                   let uu____3561 = FStar_Syntax_Subst.compress t1'  in
                   uu____3561.FStar_Syntax_Syntax.n  in
                 match uu____3560 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3576 -> aux true t1'
                 | uu____3584 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3599 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3630 =
                   let uu____3631 = FStar_Syntax_Subst.compress t1'  in
                   uu____3631.FStar_Syntax_Syntax.n  in
                 match uu____3630 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3646 -> aux true t1'
                 | uu____3654 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3669 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3716 =
                   let uu____3717 = FStar_Syntax_Subst.compress t1'  in
                   uu____3717.FStar_Syntax_Syntax.n  in
                 match uu____3716 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3732 -> aux true t1'
                 | uu____3740 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3755 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3770 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3785 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3800 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3815 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3844 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3877 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3898 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3925 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3953 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3990 ->
              let uu____3997 =
                let uu____3999 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4001 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3999 uu____4001
                 in
              failwith uu____3997
          | FStar_Syntax_Syntax.Tm_ascribed uu____4016 ->
              let uu____4043 =
                let uu____4045 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4047 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4045 uu____4047
                 in
              failwith uu____4043
          | FStar_Syntax_Syntax.Tm_delayed uu____4062 ->
              let uu____4077 =
                let uu____4079 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4081 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4079 uu____4081
                 in
              failwith uu____4077
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4096 =
                let uu____4098 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4100 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4098 uu____4100
                 in
              failwith uu____4096
           in
        let uu____4115 = whnf env t1  in aux false uu____4115
  
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
      let uu____4160 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4160 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4201 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4201, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta  ->
    fun env  ->
      fun t  ->
        let uu____4228 = base_and_refinement_maybe_delta delta env t  in
        match uu____4228 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4288  ->
    match uu____4288 with
    | (t_base,refopt) ->
        let uu____4319 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4319 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4361 =
      let uu____4365 =
        let uu____4368 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4393  ->
                  match uu____4393 with | (uu____4401,uu____4402,x) -> x))
           in
        FStar_List.append wl.attempting uu____4368  in
      FStar_List.map (wl_prob_to_string wl) uu____4365  in
    FStar_All.pipe_right uu____4361 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'uuuuuu4423 .
    ('uuuuuu4423 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4435  ->
    match uu____4435 with
    | (uu____4442,c,args) ->
        let uu____4445 = print_ctx_uvar c  in
        let uu____4447 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4445 uu____4447
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4457 = FStar_Syntax_Util.head_and_args t  in
    match uu____4457 with
    | (head,_args) ->
        let uu____4501 =
          let uu____4502 = FStar_Syntax_Subst.compress head  in
          uu____4502.FStar_Syntax_Syntax.n  in
        (match uu____4501 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4506 -> true
         | uu____4520 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4528 = FStar_Syntax_Util.head_and_args t  in
    match uu____4528 with
    | (head,_args) ->
        let uu____4571 =
          let uu____4572 = FStar_Syntax_Subst.compress head  in
          uu____4572.FStar_Syntax_Syntax.n  in
        (match uu____4571 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4576) -> u
         | uu____4593 -> failwith "Not a flex-uvar")
  
let (ensure_no_uvar_subst :
  FStar_Syntax_Syntax.term ->
    worklist -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun t0  ->
    fun wl  ->
      let bv_not_affected_by s x =
        let t_x = FStar_Syntax_Syntax.bv_to_name x  in
        let t_x' = FStar_Syntax_Subst.subst' s t_x  in
        let uu____4629 =
          let uu____4630 = FStar_Syntax_Subst.compress t_x'  in
          uu____4630.FStar_Syntax_Syntax.n  in
        match uu____4629 with
        | FStar_Syntax_Syntax.Tm_name y -> FStar_Syntax_Syntax.bv_eq x y
        | uu____4635 -> false  in
      let binding_not_affected_by s b =
        match b with
        | FStar_Syntax_Syntax.Binding_var x -> bv_not_affected_by s x
        | uu____4651 -> true  in
      let uu____4653 = FStar_Syntax_Util.head_and_args t0  in
      match uu____4653 with
      | (head,args) ->
          let uu____4700 =
            let uu____4701 = FStar_Syntax_Subst.compress head  in
            uu____4701.FStar_Syntax_Syntax.n  in
          (match uu____4700 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4709)) -> (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,uu____4725) when
               FStar_List.isEmpty uv.FStar_Syntax_Syntax.ctx_uvar_binders ->
               (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4766 =
                 FStar_Common.max_suffix (binding_not_affected_by s)
                   uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               (match uu____4766 with
                | (gamma_aff,new_gamma) ->
                    (match gamma_aff with
                     | [] -> (t0, wl)
                     | uu____4793 ->
                         let dom_binders =
                           FStar_TypeChecker_Env.binders_of_bindings
                             gamma_aff
                            in
                         let uu____4797 =
                           let uu____4804 =
                             FStar_TypeChecker_Env.binders_of_bindings
                               new_gamma
                              in
                           let uu____4813 =
                             let uu____4816 =
                               FStar_Syntax_Syntax.mk_Total
                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             FStar_Syntax_Util.arrow dom_binders uu____4816
                              in
                           new_uvar
                             (Prims.op_Hat
                                uv.FStar_Syntax_Syntax.ctx_uvar_reason
                                "; force delayed") wl
                             t0.FStar_Syntax_Syntax.pos new_gamma uu____4804
                             uu____4813
                             uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                             uv.FStar_Syntax_Syntax.ctx_uvar_meta
                            in
                         (match uu____4797 with
                          | (v,t_v,wl1) ->
                              let args_sol =
                                FStar_List.map
                                  (fun uu____4852  ->
                                     match uu____4852 with
                                     | (x,i) ->
                                         let uu____4871 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____4871, i)) dom_binders
                                 in
                              let sol =
                                FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                                  t0.FStar_Syntax_Syntax.pos
                                 in
                              (FStar_Syntax_Util.set_uvar
                                 uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                               (let args_sol_s =
                                  FStar_List.map
                                    (fun uu____4901  ->
                                       match uu____4901 with
                                       | (a,i) ->
                                           let uu____4920 =
                                             FStar_Syntax_Subst.subst' s a
                                              in
                                           (uu____4920, i)) args_sol
                                   in
                                let t =
                                  FStar_Syntax_Syntax.mk_Tm_app t_v
                                    (FStar_List.append args_sol_s args)
                                    t0.FStar_Syntax_Syntax.pos
                                   in
                                (t, wl1))))))
           | uu____4930 ->
               failwith "ensure_no_uvar_subst: expected a uvar at the head")
  
let (destruct_flex_t' : FStar_Syntax_Syntax.term -> flex_t) =
  fun t  ->
    let uu____4942 = FStar_Syntax_Util.head_and_args t  in
    match uu____4942 with
    | (head,args) ->
        let uu____4985 =
          let uu____4986 = FStar_Syntax_Subst.compress head  in
          uu____4986.FStar_Syntax_Syntax.n  in
        (match uu____4985 with
         | FStar_Syntax_Syntax.Tm_uvar (uv,s) -> (t, uv, args)
         | uu____5007 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term -> worklist -> (flex_t * worklist)) =
  fun t  ->
    fun wl  ->
      let uu____5028 = ensure_no_uvar_subst t wl  in
      match uu____5028 with
      | (t1,wl1) ->
          let uu____5039 = destruct_flex_t' t1  in (uu____5039, wl1)
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____5056 =
          let uu____5079 =
            let uu____5080 = FStar_Syntax_Subst.compress k  in
            uu____5080.FStar_Syntax_Syntax.n  in
          match uu____5079 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5162 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5162)
              else
                (let uu____5197 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5197 with
                 | (ys',t1,uu____5230) ->
                     let uu____5235 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5235))
          | uu____5274 ->
              let uu____5275 =
                let uu____5280 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5280)  in
              ((ys, t), uu____5275)
           in
        match uu____5056 with
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
                 let uu____5375 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5375 c  in
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
               (let uu____5453 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5453
                then
                  let uu____5458 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5460 = print_ctx_uvar uv  in
                  let uu____5462 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5458 uu____5460 uu____5462
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5471 =
                   let uu____5473 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5473  in
                 let uu____5476 =
                   let uu____5479 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5479
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5471 uu____5476 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail uu____5512 =
               let uu____5513 =
                 let uu____5515 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5517 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5515 uu____5517
                  in
               failwith uu____5513  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5583  ->
                       match uu____5583 with
                       | (a,i) ->
                           let uu____5604 =
                             let uu____5605 = FStar_Syntax_Subst.compress a
                                in
                             uu____5605.FStar_Syntax_Syntax.n  in
                           (match uu____5604 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5631 -> (fail (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5641 =
                 let uu____5643 = is_flex g  in Prims.op_Negation uu____5643
                  in
               if uu____5641
               then (if resolve_ok then wl else (fail (); wl))
               else
                 (let uu____5652 = destruct_flex_t g wl  in
                  match uu____5652 with
                  | ((uu____5657,uv1,args),wl1) ->
                      ((let uu____5662 = args_as_binders args  in
                        assign_solution uu____5662 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___735_5664 = wl1  in
              {
                attempting = (uu___735_5664.attempting);
                wl_deferred = (uu___735_5664.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___735_5664.defer_ok);
                smt_ok = (uu___735_5664.smt_ok);
                umax_heuristic_ok = (uu___735_5664.umax_heuristic_ok);
                tcenv = (uu___735_5664.tcenv);
                wl_implicits = (uu___735_5664.wl_implicits);
                repr_subcomp_allowed = (uu___735_5664.repr_subcomp_allowed)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5689 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5689
         then
           let uu____5694 = FStar_Util.string_of_int pid  in
           let uu____5696 = uvis_to_string wl.tcenv sol  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5694 uu____5696
         else ());
        commit sol;
        (let uu___743_5702 = wl  in
         {
           attempting = (uu___743_5702.attempting);
           wl_deferred = (uu___743_5702.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___743_5702.defer_ok);
           smt_ok = (uu___743_5702.smt_ok);
           umax_heuristic_ok = (uu___743_5702.umax_heuristic_ok);
           tcenv = (uu___743_5702.tcenv);
           wl_implicits = (uu___743_5702.wl_implicits);
           repr_subcomp_allowed = (uu___743_5702.repr_subcomp_allowed)
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
          (let uu____5738 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____5738
           then
             let uu____5743 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____5747 = uvis_to_string wl.tcenv uvis  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5743 uu____5747
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
        let uu____5774 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5774 FStar_Util.set_elements  in
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
      let uu____5814 = occurs uk t  in
      match uu____5814 with
      | (uvars,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5853 =
                 let uu____5855 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5857 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5855 uu____5857
                  in
               FStar_Pervasives_Native.Some uu____5853)
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
          let uu____5968 = FStar_Syntax_Syntax.bv_eq b b'  in
          if uu____5968
          then
            let uu____5979 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5979 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____6030 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6087  ->
             match uu____6087 with
             | (x,uu____6099) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6117 = FStar_List.last bs  in
      match uu____6117 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6141) ->
          let uu____6152 =
            FStar_Util.prefix_until
              (fun uu___18_6167  ->
                 match uu___18_6167 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6170 -> false) g
             in
          (match uu____6152 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6184,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6221 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6221 with
        | (pfx,uu____6231) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6243 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6243 with
             | (uu____6251,src',wl1) ->
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
                 | uu____6365 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6366 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6430  ->
                  fun uu____6431  ->
                    match (uu____6430, uu____6431) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6534 =
                          let uu____6536 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6536
                           in
                        if uu____6534
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6570 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6570
                           then
                             let uu____6587 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6587)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6366 with | (isect,uu____6637) -> FStar_List.rev isect
  
let binders_eq :
  'uuuuuu6673 'uuuuuu6674 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu6673) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6674) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6732  ->
              fun uu____6733  ->
                match (uu____6732, uu____6733) with
                | ((a,uu____6752),(b,uu____6754)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'uuuuuu6770 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6770) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6801  ->
           match uu____6801 with
           | (y,uu____6808) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'uuuuuu6818 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6818) Prims.list ->
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
                   let uu____6980 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6980
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____7013 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7065 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7109 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7130 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_7138  ->
    match uu___19_7138 with
    | MisMatch (d1,d2) ->
        let uu____7150 =
          let uu____7152 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7154 =
            let uu____7156 =
              let uu____7158 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7158 ")"  in
            Prims.op_Hat ") (" uu____7156  in
          Prims.op_Hat uu____7152 uu____7154  in
        Prims.op_Hat "MisMatch (" uu____7150
    | HeadMatch u ->
        let uu____7165 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7165
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___20_7174  ->
    match uu___20_7174 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7191 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv  in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____7206 =
            (let uu____7212 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule
                in
             let uu____7214 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             uu____7212 = uu____7214) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
             in
          if uu____7206 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7223 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7223 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7234 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7258 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7268 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7287 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7287
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7288 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7289 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7290 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7303 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7317 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7341) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7347,uu____7348) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7390) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7415;
             FStar_Syntax_Syntax.index = uu____7416;
             FStar_Syntax_Syntax.sort = t2;_},uu____7418)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7426 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7427 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7428 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7443 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7450 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7470 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7470
  
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
           { FStar_Syntax_Syntax.blob = uu____7489;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7490;
             FStar_Syntax_Syntax.ltyp = uu____7491;
             FStar_Syntax_Syntax.rng = uu____7492;_},uu____7493)
            ->
            let uu____7504 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7504 t21
        | (uu____7505,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7506;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7507;
             FStar_Syntax_Syntax.ltyp = uu____7508;
             FStar_Syntax_Syntax.rng = uu____7509;_})
            ->
            let uu____7520 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7520
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7523 = FStar_Syntax_Syntax.bv_eq x y  in
            if uu____7523
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7534 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7534
            then FullMatch
            else
              (let uu____7539 =
                 let uu____7548 =
                   let uu____7551 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7551  in
                 let uu____7552 =
                   let uu____7555 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7555  in
                 (uu____7548, uu____7552)  in
               MisMatch uu____7539)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7561),FStar_Syntax_Syntax.Tm_uinst (g,uu____7563)) ->
            let uu____7572 = head_matches env f g  in
            FStar_All.pipe_right uu____7572 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7573) -> HeadMatch true
        | (uu____7575,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7579 = FStar_Const.eq_const c d  in
            if uu____7579
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7589),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7591)) ->
            let uu____7624 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7624
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7634),FStar_Syntax_Syntax.Tm_refine (y,uu____7636)) ->
            let uu____7645 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7645 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7647),uu____7648) ->
            let uu____7653 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7653 head_match
        | (uu____7654,FStar_Syntax_Syntax.Tm_refine (x,uu____7656)) ->
            let uu____7661 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7661 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7662,FStar_Syntax_Syntax.Tm_type
           uu____7663) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7665,FStar_Syntax_Syntax.Tm_arrow uu____7666) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head,uu____7697),FStar_Syntax_Syntax.Tm_app (head',uu____7699))
            ->
            let uu____7748 = head_matches env head head'  in
            FStar_All.pipe_right uu____7748 head_match
        | (FStar_Syntax_Syntax.Tm_app (head,uu____7750),uu____7751) ->
            let uu____7776 = head_matches env head t21  in
            FStar_All.pipe_right uu____7776 head_match
        | (uu____7777,FStar_Syntax_Syntax.Tm_app (head,uu____7779)) ->
            let uu____7804 = head_matches env t11 head  in
            FStar_All.pipe_right uu____7804 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7805,FStar_Syntax_Syntax.Tm_let
           uu____7806) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7834,FStar_Syntax_Syntax.Tm_match uu____7835) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7881,FStar_Syntax_Syntax.Tm_abs
           uu____7882) -> HeadMatch true
        | uu____7920 ->
            let uu____7925 =
              let uu____7934 = delta_depth_of_term env t11  in
              let uu____7937 = delta_depth_of_term env t21  in
              (uu____7934, uu____7937)  in
            MisMatch uu____7925
  
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
              let uu____8006 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____8006  in
            (let uu____8008 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8008
             then
               let uu____8013 = FStar_Syntax_Print.term_to_string t  in
               let uu____8015 = FStar_Syntax_Print.term_to_string head  in
               FStar_Util.print2 "Head of %s is %s\n" uu____8013 uu____8015
             else ());
            (let uu____8020 =
               let uu____8021 = FStar_Syntax_Util.un_uinst head  in
               uu____8021.FStar_Syntax_Syntax.n  in
             match uu____8020 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____8027 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____8027 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8041 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____8041
                        then
                          let uu____8046 =
                            FStar_Syntax_Print.term_to_string head  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8046
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8051 ->
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
                      let uu____8069 =
                        let uu____8071 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8071 = FStar_Syntax_Util.Equal  in
                      if uu____8069
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8078 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8078
                          then
                            let uu____8083 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8085 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8083
                              uu____8085
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8090 -> FStar_Pervasives_Native.None)
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
            (let uu____8242 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8242
             then
               let uu____8247 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8249 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8251 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8247
                 uu____8249 uu____8251
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8279 =
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
               match uu____8279 with
               | (t12,t22) -> aux retry (n_delta + Prims.int_one) t12 t22  in
             let reduce_both_and_try_again d r1 =
               let uu____8327 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8327 with
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
                  uu____8365),uu____8366)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8387 =
                      let uu____8396 = maybe_inline t11  in
                      let uu____8399 = maybe_inline t21  in
                      (uu____8396, uu____8399)  in
                    match uu____8387 with
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
                 (uu____8442,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8443))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8464 =
                      let uu____8473 = maybe_inline t11  in
                      let uu____8476 = maybe_inline t21  in
                      (uu____8473, uu____8476)  in
                    match uu____8464 with
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
             | MisMatch uu____8531 -> fail n_delta r t11 t21
             | uu____8540 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8555 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8555
           then
             let uu____8560 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8562 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8564 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8572 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8589 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8589
                    (fun uu____8624  ->
                       match uu____8624 with
                       | (t11,t21) ->
                           let uu____8632 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8634 =
                             let uu____8636 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8636  in
                           Prims.op_Hat uu____8632 uu____8634))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8560 uu____8562 uu____8564 uu____8572
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8653 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8653 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_8668  ->
    match uu___21_8668 with
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
      let uu___1232_8717 = p  in
      let uu____8720 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8721 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1232_8717.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8720;
        FStar_TypeChecker_Common.relation =
          (uu___1232_8717.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8721;
        FStar_TypeChecker_Common.element =
          (uu___1232_8717.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1232_8717.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1232_8717.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1232_8717.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1232_8717.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1232_8717.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8736 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8736
            (fun uu____8741  -> FStar_TypeChecker_Common.TProb uu____8741)
      | FStar_TypeChecker_Common.CProb uu____8742 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8765 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8765 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8773 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8773 with
           | (lh,lhs_args) ->
               let uu____8820 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8820 with
                | (rh,rhs_args) ->
                    let uu____8867 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8880,FStar_Syntax_Syntax.Tm_uvar uu____8881)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8970 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8997,uu____8998)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9013,FStar_Syntax_Syntax.Tm_uvar uu____9014)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9029,FStar_Syntax_Syntax.Tm_arrow uu____9030)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1283_9060 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1283_9060.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1283_9060.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1283_9060.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1283_9060.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1283_9060.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1283_9060.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1283_9060.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1283_9060.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1283_9060.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9063,FStar_Syntax_Syntax.Tm_type uu____9064)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1283_9080 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1283_9080.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1283_9080.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1283_9080.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1283_9080.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1283_9080.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1283_9080.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1283_9080.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1283_9080.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1283_9080.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9083,FStar_Syntax_Syntax.Tm_uvar uu____9084)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1283_9100 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1283_9100.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1283_9100.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1283_9100.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1283_9100.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1283_9100.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1283_9100.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1283_9100.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1283_9100.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1283_9100.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9103,FStar_Syntax_Syntax.Tm_uvar uu____9104)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9119,uu____9120)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9135,FStar_Syntax_Syntax.Tm_uvar uu____9136)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9151,uu____9152) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8867 with
                     | (rank,tp1) ->
                         let uu____9165 =
                           FStar_All.pipe_right
                             (let uu___1303_9169 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1303_9169.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1303_9169.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1303_9169.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1303_9169.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1303_9169.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1303_9169.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1303_9169.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1303_9169.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1303_9169.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____9172  ->
                                FStar_TypeChecker_Common.TProb uu____9172)
                            in
                         (rank, uu____9165))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9176 =
            FStar_All.pipe_right
              (let uu___1307_9180 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1307_9180.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1307_9180.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1307_9180.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1307_9180.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1307_9180.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1307_9180.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1307_9180.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1307_9180.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1307_9180.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____9183  -> FStar_TypeChecker_Common.CProb uu____9183)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9176)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9243 probs =
      match uu____9243 with
      | (min_rank,min,out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9324 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____9345 = rank wl.tcenv hd  in
               (match uu____9345 with
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
                      (let uu____9406 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9411 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9411)
                          in
                       if uu____9406
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
          let uu____9484 = FStar_Syntax_Util.head_and_args t  in
          match uu____9484 with
          | (hd,uu____9503) ->
              let uu____9528 =
                let uu____9529 = FStar_Syntax_Subst.compress hd  in
                uu____9529.FStar_Syntax_Syntax.n  in
              (match uu____9528 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9534) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9569  ->
                           match uu____9569 with
                           | (y,uu____9578) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9601  ->
                                       match uu____9601 with
                                       | (x,uu____9610) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9615 -> false)
           in
        let uu____9617 = rank tcenv p  in
        match uu____9617 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9626 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9707 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9726 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9745 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9762 = FStar_Thunk.mkv s  in UFailed uu____9762 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9777 = mklstr s  in UFailed uu____9777 
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
                        let uu____9828 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9828 with
                        | (k,uu____9836) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9851 -> false)))
            | uu____9853 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9905 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  FStar_Syntax_Util.eq_univs uv1 uv2))
                           in
                        if uu____9905 then uv1 :: uvs else uvs) [])
               in
            let filter =
              FStar_List.filter
                (fun u  ->
                   let uu____9929 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  -> FStar_Syntax_Util.eq_univs u u'))
                      in
                   Prims.op_Negation uu____9929)
               in
            let uu____9936 = filter u12  in
            let uu____9939 = filter u22  in (uu____9936, uu____9939)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9974 = filter_out_common_univs us1 us2  in
                   (match uu____9974 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____10034 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____10034 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10037 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10054  ->
                               let uu____10055 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10057 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10055 uu____10057))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10083 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10083 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10109 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10109 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10112 ->
                   ufailed_thunk
                     (fun uu____10123  ->
                        let uu____10124 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10126 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10124 uu____10126 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10129,uu____10130) ->
              let uu____10132 =
                let uu____10134 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10136 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10134 uu____10136
                 in
              failwith uu____10132
          | (FStar_Syntax_Syntax.U_unknown ,uu____10139) ->
              let uu____10140 =
                let uu____10142 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10144 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10142 uu____10144
                 in
              failwith uu____10140
          | (uu____10147,FStar_Syntax_Syntax.U_bvar uu____10148) ->
              let uu____10150 =
                let uu____10152 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10154 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10152 uu____10154
                 in
              failwith uu____10150
          | (uu____10157,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10158 =
                let uu____10160 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10162 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10160 uu____10162
                 in
              failwith uu____10158
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              let uu____10167 =
                let uu____10169 = FStar_Ident.string_of_id x  in
                let uu____10171 = FStar_Ident.string_of_id y  in
                uu____10169 = uu____10171  in
              if uu____10167
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10202 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10202
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10221 = occurs_univ v1 u3  in
              if uu____10221
              then
                let uu____10224 =
                  let uu____10226 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10228 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10226 uu____10228
                   in
                try_umax_components u11 u21 uu____10224
              else
                (let uu____10233 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10233)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10247 = occurs_univ v1 u3  in
              if uu____10247
              then
                let uu____10250 =
                  let uu____10252 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10254 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10252 uu____10254
                   in
                try_umax_components u11 u21 uu____10250
              else
                (let uu____10259 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10259)
          | (FStar_Syntax_Syntax.U_max uu____10260,uu____10261) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10269 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10269
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10275,FStar_Syntax_Syntax.U_max uu____10276) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10284 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10284
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10290,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10292,FStar_Syntax_Syntax.U_name uu____10293) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10295) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10297) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10299,FStar_Syntax_Syntax.U_succ uu____10300) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10302,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10409 = bc1  in
      match uu____10409 with
      | (bs1,mk_cod1) ->
          let uu____10453 = bc2  in
          (match uu____10453 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10564 = aux xs ys  in
                     (match uu____10564 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10647 =
                       let uu____10654 = mk_cod1 xs  in ([], uu____10654)  in
                     let uu____10657 =
                       let uu____10664 = mk_cod2 ys  in ([], uu____10664)  in
                     (uu____10647, uu____10657)
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
                  let uu____10733 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10733 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10736 =
                    let uu____10737 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10737 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10736
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10742 = has_type_guard t1 t2  in (uu____10742, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10743 = has_type_guard t2 t1  in (uu____10743, wl)
  
let is_flex_pat :
  'uuuuuu10753 'uuuuuu10754 'uuuuuu10755 .
    ('uuuuuu10753 * 'uuuuuu10754 * 'uuuuuu10755 Prims.list) -> Prims.bool
  =
  fun uu___22_10769  ->
    match uu___22_10769 with
    | (uu____10778,uu____10779,[]) -> true
    | uu____10783 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10816 = f  in
      match uu____10816 with
      | (uu____10823,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10824;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10825;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10828;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10829;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10830;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10831;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10903  ->
                 match uu____10903 with
                 | (y,uu____10912) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11066 =
                  let uu____11081 =
                    let uu____11084 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11084  in
                  ((FStar_List.rev pat_binders), uu____11081)  in
                FStar_Pervasives_Native.Some uu____11066
            | (uu____11117,[]) ->
                let uu____11148 =
                  let uu____11163 =
                    let uu____11166 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11166  in
                  ((FStar_List.rev pat_binders), uu____11163)  in
                FStar_Pervasives_Native.Some uu____11148
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11257 =
                  let uu____11258 = FStar_Syntax_Subst.compress a  in
                  uu____11258.FStar_Syntax_Syntax.n  in
                (match uu____11257 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11278 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11278
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1635_11308 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1635_11308.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1635_11308.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst =
                          let uu____11312 =
                            let uu____11313 =
                              let uu____11320 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11320)  in
                            FStar_Syntax_Syntax.NT uu____11313  in
                          [uu____11312]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1  in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res  in
                        aux
                          (((let uu___1641_11336 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1641_11336.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1641_11336.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11337 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11377 =
                  let uu____11384 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11384  in
                (match uu____11377 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11443 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11468 ->
               let uu____11469 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11469 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11765 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11765
       then
         let uu____11770 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11770
       else ());
      (let uu____11776 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____11776
       then
         let uu____11781 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11781
       else ());
      (let uu____11786 = next_prob probs  in
       match uu____11786 with
       | FStar_Pervasives_Native.Some (hd,tl,rank1) ->
           let probs1 =
             let uu___1668_11813 = probs  in
             {
               attempting = tl;
               wl_deferred = (uu___1668_11813.wl_deferred);
               ctr = (uu___1668_11813.ctr);
               defer_ok = (uu___1668_11813.defer_ok);
               smt_ok = (uu___1668_11813.smt_ok);
               umax_heuristic_ok = (uu___1668_11813.umax_heuristic_ok);
               tcenv = (uu___1668_11813.tcenv);
               wl_implicits = (uu___1668_11813.wl_implicits);
               repr_subcomp_allowed = (uu___1668_11813.repr_subcomp_allowed)
             }  in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11822 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11822
                 then
                   let uu____11825 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1  in
                   solve env uu____11825
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
                       (let uu____11832 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd
                            probs1
                           in
                        solve env uu____11832)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1680_11838 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1680_11838.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1680_11838.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1680_11838.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1680_11838.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1680_11838.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1680_11838.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1680_11838.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1680_11838.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1680_11838.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11863 ->
                let uu____11873 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11938  ->
                          match uu____11938 with
                          | (c,uu____11948,uu____11949) -> c < probs.ctr))
                   in
                (match uu____11873 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11997 =
                            let uu____12002 =
                              FStar_List.map
                                (fun uu____12023  ->
                                   match uu____12023 with
                                   | (uu____12039,x,y) ->
                                       let uu____12050 = FStar_Thunk.force x
                                          in
                                       (uu____12050, y)) probs.wl_deferred
                               in
                            (uu____12002, (probs.wl_implicits))  in
                          Success uu____11997
                      | uu____12054 ->
                          let uu____12064 =
                            let uu___1698_12065 = probs  in
                            let uu____12066 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12087  ->
                                      match uu____12087 with
                                      | (uu____12095,uu____12096,y) -> y))
                               in
                            {
                              attempting = uu____12066;
                              wl_deferred = rest;
                              ctr = (uu___1698_12065.ctr);
                              defer_ok = (uu___1698_12065.defer_ok);
                              smt_ok = (uu___1698_12065.smt_ok);
                              umax_heuristic_ok =
                                (uu___1698_12065.umax_heuristic_ok);
                              tcenv = (uu___1698_12065.tcenv);
                              wl_implicits = (uu___1698_12065.wl_implicits);
                              repr_subcomp_allowed =
                                (uu___1698_12065.repr_subcomp_allowed)
                            }  in
                          solve env uu____12064))))

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
            let uu____12105 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12105 with
            | USolved wl1 ->
                let uu____12107 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12107
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12110 = defer_lit "" orig wl1  in
                solve env uu____12110

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
                  let uu____12161 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12161 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12164 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12177;
                  FStar_Syntax_Syntax.vars = uu____12178;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12181;
                  FStar_Syntax_Syntax.vars = uu____12182;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12195,uu____12196) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12204,FStar_Syntax_Syntax.Tm_uinst uu____12205) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12213 -> USolved wl

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
            ((let uu____12224 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12224
              then
                let uu____12229 = prob_to_string env orig  in
                let uu____12231 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12229 uu____12231
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
               let uu____12324 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12324 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12379 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12379
                then
                  let uu____12384 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12386 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12384 uu____12386
                else ());
               (let uu____12391 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12391 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12437 = eq_prob t1 t2 wl2  in
                         (match uu____12437 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12458 ->
                         let uu____12467 = eq_prob t1 t2 wl2  in
                         (match uu____12467 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12517 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12532 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12533 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12532, uu____12533)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12538 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12539 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12538, uu____12539)
                            in
                         (match uu____12517 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12570 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12570 with
                                | (t1_hd,t1_args) ->
                                    let uu____12615 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12615 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12681 =
                                              let uu____12688 =
                                                let uu____12699 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12699 :: t1_args  in
                                              let uu____12716 =
                                                let uu____12725 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12725 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12774  ->
                                                   fun uu____12775  ->
                                                     fun uu____12776  ->
                                                       match (uu____12774,
                                                               uu____12775,
                                                               uu____12776)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12826),
                                                          (a2,uu____12828))
                                                           ->
                                                           let uu____12865 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12865
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12688
                                                uu____12716
                                               in
                                            match uu____12681 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1852_12891 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1852_12891.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1852_12891.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1852_12891.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1852_12891.repr_subcomp_allowed)
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12902 =
                                                  solve env1 wl'  in
                                                (match uu____12902 with
                                                 | Success (uu____12905,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1861_12909
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1861_12909.attempting);
                                                            wl_deferred =
                                                              (uu___1861_12909.wl_deferred);
                                                            ctr =
                                                              (uu___1861_12909.ctr);
                                                            defer_ok =
                                                              (uu___1861_12909.defer_ok);
                                                            smt_ok =
                                                              (uu___1861_12909.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1861_12909.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1861_12909.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps);
                                                            repr_subcomp_allowed
                                                              =
                                                              (uu___1861_12909.repr_subcomp_allowed)
                                                          })))
                                                 | Failed uu____12910 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12942 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12942 with
                                | (t1_base,p1_opt) ->
                                    let uu____12978 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12978 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____13077 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13077
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
                                               let uu____13130 =
                                                 op phi11 phi21  in
                                               refine x1 uu____13130
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
                                               let uu____13162 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13162
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
                                               let uu____13194 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13194
                                           | uu____13197 -> t_base  in
                                         let uu____13214 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13214 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13228 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13228, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13235 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13235 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13271 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13271 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13307 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13307
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
                              let uu____13331 = combine t11 t21 wl2  in
                              (match uu____13331 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13364 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13364
                                     then
                                       let uu____13369 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13369
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13411 ts1 =
               match uu____13411 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13474 = pairwise out t wl2  in
                        (match uu____13474 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13510 =
               let uu____13521 = FStar_List.hd ts  in (uu____13521, [], wl1)
                in
             let uu____13530 = FStar_List.tl ts  in
             aux uu____13510 uu____13530  in
           let uu____13537 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13537 with
           | (this_flex,this_rigid) ->
               let uu____13563 =
                 let uu____13564 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13564.FStar_Syntax_Syntax.n  in
               (match uu____13563 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13589 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13589
                    then
                      let uu____13592 = destruct_flex_t this_flex wl  in
                      (match uu____13592 with
                       | (flex,wl1) ->
                           let uu____13599 = quasi_pattern env flex  in
                           (match uu____13599 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t1)
                                ->
                                ((let uu____13618 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13618
                                  then
                                    let uu____13623 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13623
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13630 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1963_13633 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1963_13633.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1963_13633.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1963_13633.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1963_13633.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1963_13633.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1963_13633.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1963_13633.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1963_13633.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1963_13633.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13630)
                | uu____13634 ->
                    ((let uu____13636 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13636
                      then
                        let uu____13641 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13641
                      else ());
                     (let uu____13646 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13646 with
                      | (u,_args) ->
                          let uu____13689 =
                            let uu____13690 = FStar_Syntax_Subst.compress u
                               in
                            uu____13690.FStar_Syntax_Syntax.n  in
                          (match uu____13689 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv t =
                                 let uu____13718 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13718 with
                                 | (u',uu____13737) ->
                                     let uu____13762 =
                                       let uu____13763 = whnf env u'  in
                                       uu____13763.FStar_Syntax_Syntax.n  in
                                     (match uu____13762 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13785 -> false)
                                  in
                               let uu____13787 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_13810  ->
                                         match uu___23_13810 with
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
                                              | uu____13824 -> false)
                                         | uu____13828 -> false))
                                  in
                               (match uu____13787 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13843 = whnf env this_rigid
                                         in
                                      let uu____13844 =
                                        FStar_List.collect
                                          (fun uu___24_13850  ->
                                             match uu___24_13850 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13856 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13856]
                                             | uu____13860 -> [])
                                          bounds_probs
                                         in
                                      uu____13843 :: uu____13844  in
                                    let uu____13861 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13861 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13894 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13909 =
                                               let uu____13910 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13910.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13909 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13922 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13922)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13933 -> bound  in
                                           let uu____13934 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13934)  in
                                         (match uu____13894 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13969 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13969
                                                then
                                                  let wl'1 =
                                                    let uu___2023_13975 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2023_13975.wl_deferred);
                                                      ctr =
                                                        (uu___2023_13975.ctr);
                                                      defer_ok =
                                                        (uu___2023_13975.defer_ok);
                                                      smt_ok =
                                                        (uu___2023_13975.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2023_13975.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2023_13975.tcenv);
                                                      wl_implicits =
                                                        (uu___2023_13975.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2023_13975.repr_subcomp_allowed)
                                                    }  in
                                                  let uu____13976 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13976
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13982 =
                                                  solve_t env eq_prob
                                                    (let uu___2028_13984 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2028_13984.wl_deferred);
                                                       ctr =
                                                         (uu___2028_13984.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2028_13984.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2028_13984.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2028_13984.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2028_13984.repr_subcomp_allowed)
                                                     })
                                                   in
                                                match uu____13982 with
                                                | Success (uu____13986,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2034_13989 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2034_13989.wl_deferred);
                                                        ctr =
                                                          (uu___2034_13989.ctr);
                                                        defer_ok =
                                                          (uu___2034_13989.defer_ok);
                                                        smt_ok =
                                                          (uu___2034_13989.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2034_13989.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2034_13989.tcenv);
                                                        wl_implicits =
                                                          (uu___2034_13989.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2034_13989.repr_subcomp_allowed)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2037_13991 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2037_13991.attempting);
                                                        wl_deferred =
                                                          (uu___2037_13991.wl_deferred);
                                                        ctr =
                                                          (uu___2037_13991.ctr);
                                                        defer_ok =
                                                          (uu___2037_13991.defer_ok);
                                                        smt_ok =
                                                          (uu___2037_13991.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2037_13991.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2037_13991.tcenv);
                                                        wl_implicits =
                                                          (FStar_List.append
                                                             wl'.wl_implicits
                                                             imps);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2037_13991.repr_subcomp_allowed)
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
                                                    let uu____14007 =
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
                                                    ((let uu____14019 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____14019
                                                      then
                                                        let uu____14024 =
                                                          let uu____14026 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____14026
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14024
                                                      else ());
                                                     (let uu____14039 =
                                                        let uu____14054 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14054)
                                                         in
                                                      match uu____14039 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14076))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14102 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14102
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
                                                                  let uu____14122
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14122))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14147 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14147
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
                                                                    let uu____14167
                                                                    =
                                                                    let uu____14172
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14172
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14167
                                                                    [] wl2
                                                                     in
                                                                  let uu____14178
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14178))))
                                                      | uu____14179 ->
                                                          let uu____14194 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14194 p)))))))
                           | uu____14201 when flip ->
                               let uu____14202 =
                                 let uu____14204 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14206 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14204 uu____14206
                                  in
                               failwith uu____14202
                           | uu____14209 ->
                               let uu____14210 =
                                 let uu____14212 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14214 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14212 uu____14214
                                  in
                               failwith uu____14210)))))

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
                      (fun uu____14250  ->
                         match uu____14250 with
                         | (x,i) ->
                             let uu____14269 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14269, i)) bs_lhs
                     in
                  let uu____14272 = lhs  in
                  match uu____14272 with
                  | (uu____14273,u_lhs,uu____14275) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14372 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14382 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14382, univ)
                             in
                          match uu____14372 with
                          | (k,univ) ->
                              let uu____14389 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14389 with
                               | (uu____14406,u,wl3) ->
                                   let uu____14409 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14409, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14435 =
                              let uu____14448 =
                                let uu____14459 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14459 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14510  ->
                                   fun uu____14511  ->
                                     match (uu____14510, uu____14511) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14612 =
                                           let uu____14619 =
                                             let uu____14622 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14622
                                              in
                                           copy_uvar u_lhs [] uu____14619 wl2
                                            in
                                         (match uu____14612 with
                                          | (uu____14651,t_a,wl3) ->
                                              let uu____14654 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14654 with
                                               | (uu____14673,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14448
                                ([], wl1)
                               in
                            (match uu____14435 with
                             | (out_args,wl2) ->
                                 let nodec flags =
                                   FStar_List.filter
                                     (fun uu___25_14742  ->
                                        match uu___25_14742 with
                                        | FStar_Syntax_Syntax.DECREASES
                                            uu____14744 -> false
                                        | uu____14748 -> true) flags
                                    in
                                 let ct' =
                                   let uu___2154_14751 = ct  in
                                   let uu____14752 =
                                     let uu____14755 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14755
                                      in
                                   let uu____14770 = FStar_List.tl out_args
                                      in
                                   let uu____14787 =
                                     nodec ct.FStar_Syntax_Syntax.flags  in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2154_14751.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2154_14751.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14752;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14770;
                                     FStar_Syntax_Syntax.flags = uu____14787
                                   }  in
                                 ((let uu___2157_14791 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2157_14791.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2157_14791.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14794 =
                        FStar_Syntax_Util.arrow_formals_comp arrow  in
                      (match uu____14794 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14832 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14832 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14843 =
                                          let uu____14848 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14848)  in
                                        TERM uu____14843  in
                                      let uu____14849 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14849 with
                                       | (sub_prob,wl3) ->
                                           let uu____14863 =
                                             let uu____14864 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14864
                                              in
                                           solve env uu____14863))
                             | (x,imp)::formals2 ->
                                 let uu____14886 =
                                   let uu____14893 =
                                     let uu____14896 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14896
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14893 wl1
                                    in
                                 (match uu____14886 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14917 =
                                          let uu____14920 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14920
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14917 u_x
                                         in
                                      let uu____14921 =
                                        let uu____14924 =
                                          let uu____14927 =
                                            let uu____14928 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14928, imp)  in
                                          [uu____14927]  in
                                        FStar_List.append bs_terms
                                          uu____14924
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14921 formals2 wl2)
                              in
                           let uu____14955 = occurs_check u_lhs arrow  in
                           (match uu____14955 with
                            | (uu____14968,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14984 =
                                    mklstr
                                      (fun uu____14989  ->
                                         let uu____14990 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14990)
                                     in
                                  giveup_or_defer env orig wl uu____14984
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
              (let uu____15023 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____15023
               then
                 let uu____15028 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____15031 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15028 (rel_to_string (p_rel orig)) uu____15031
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15162 = rhs wl1 scope env1 subst  in
                     (match uu____15162 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15185 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15185
                            then
                              let uu____15190 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15190
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15268 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15268 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2227_15270 = hd1  in
                       let uu____15271 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2227_15270.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2227_15270.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15271
                       }  in
                     let hd21 =
                       let uu___2230_15275 = hd2  in
                       let uu____15276 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2230_15275.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2230_15275.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15276
                       }  in
                     let uu____15279 =
                       let uu____15284 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15284
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15279 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst1 =
                            let uu____15307 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15307
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15314 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1
                             in
                          (match uu____15314 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15386 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15386
                                  in
                               ((let uu____15404 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15404
                                 then
                                   let uu____15409 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15411 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15409
                                     uu____15411
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____15446 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15482 = aux wl [] env [] bs1 bs2  in
               match uu____15482 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15541 = attempt sub_probs wl2  in
                   solve env1 uu____15541)

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
            let uu___2268_15561 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2268_15561.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2268_15561.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2268_15561.repr_subcomp_allowed)
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15573 = try_solve env wl'  in
          match uu____15573 with
          | Success (uu____15574,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2277_15578 = wl  in
                  {
                    attempting = (uu___2277_15578.attempting);
                    wl_deferred = (uu___2277_15578.wl_deferred);
                    ctr = (uu___2277_15578.ctr);
                    defer_ok = (uu___2277_15578.defer_ok);
                    smt_ok = (uu___2277_15578.smt_ok);
                    umax_heuristic_ok = (uu___2277_15578.umax_heuristic_ok);
                    tcenv = (uu___2277_15578.tcenv);
                    wl_implicits = (FStar_List.append wl.wl_implicits imps);
                    repr_subcomp_allowed =
                      (uu___2277_15578.repr_subcomp_allowed)
                  }  in
                solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____15587 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15587 wl)

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
              let uu____15601 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15601 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15635 = lhs1  in
              match uu____15635 with
              | (uu____15638,ctx_u,uu____15640) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15648 ->
                        let uu____15649 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15649 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15698 = quasi_pattern env1 lhs1  in
              match uu____15698 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15732) ->
                  let uu____15737 = lhs1  in
                  (match uu____15737 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15752 = occurs_check ctx_u rhs1  in
                       (match uu____15752 with
                        | (uvars,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15803 =
                                let uu____15811 =
                                  let uu____15813 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15813
                                   in
                                FStar_Util.Inl uu____15811  in
                              (uu____15803, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15841 =
                                 let uu____15843 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15843  in
                               if uu____15841
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15870 =
                                    let uu____15878 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15878  in
                                  let uu____15884 =
                                    restrict_all_uvars ctx_u uvars wl1  in
                                  (uu____15870, uu____15884)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15928 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15928 with
              | (rhs_hd,args) ->
                  let uu____15971 = FStar_Util.prefix args  in
                  (match uu____15971 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____16041 = lhs1  in
                       (match uu____16041 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____16045 =
                              let uu____16056 =
                                let uu____16063 =
                                  let uu____16066 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____16066
                                   in
                                copy_uvar u_lhs [] uu____16063 wl1  in
                              match uu____16056 with
                              | (uu____16093,t_last_arg,wl2) ->
                                  let uu____16096 =
                                    let uu____16103 =
                                      let uu____16104 =
                                        let uu____16113 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____16113]  in
                                      FStar_List.append bs_lhs uu____16104
                                       in
                                    copy_uvar u_lhs uu____16103 t_res_lhs wl2
                                     in
                                  (match uu____16096 with
                                   | (uu____16148,lhs',wl3) ->
                                       let uu____16151 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16151 with
                                        | (uu____16168,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____16045 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16189 =
                                     let uu____16190 =
                                       let uu____16195 =
                                         let uu____16196 =
                                           let uu____16199 =
                                             let uu____16200 =
                                               FStar_Syntax_Syntax.as_arg
                                                 lhs'_last_arg
                                                in
                                             [uu____16200]  in
                                           FStar_Syntax_Syntax.mk_Tm_app lhs'
                                             uu____16199
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16196
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16195)  in
                                     TERM uu____16190  in
                                   [uu____16189]  in
                                 let uu____16225 =
                                   let uu____16232 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16232 with
                                   | (p1,wl3) ->
                                       let uu____16252 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16252 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16225 with
                                  | (sub_probs,wl3) ->
                                      let uu____16284 =
                                        let uu____16285 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16285  in
                                      solve env1 uu____16284))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16319 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16319 with
                | (uu____16337,args) ->
                    (match args with | [] -> false | uu____16373 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16392 =
                  let uu____16393 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16393.FStar_Syntax_Syntax.n  in
                match uu____16392 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16397 -> true
                | uu____16413 -> false  in
              let uu____16415 = quasi_pattern env1 lhs1  in
              match uu____16415 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    mklstr
                      (fun uu____16434  ->
                         let uu____16435 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16435)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16444 = is_app rhs1  in
                  if uu____16444
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16449 = is_arrow rhs1  in
                     if uu____16449
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          mklstr
                            (fun uu____16462  ->
                               let uu____16463 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16463)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16467 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16467
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16473 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16473
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16478 = lhs  in
                (match uu____16478 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16482 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16482 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16500 =
                              let uu____16504 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16504
                               in
                            FStar_All.pipe_right uu____16500
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16525 = occurs_check ctx_uv rhs1  in
                          (match uu____16525 with
                           | (uvars,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16554 =
                                   let uu____16555 =
                                     let uu____16557 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16557
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16555
                                    in
                                 giveup_or_defer env orig wl uu____16554
                               else
                                 (let uu____16565 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16565
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars wl  in
                                    let uu____16572 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16572
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         mklstr
                                           (fun uu____16588  ->
                                              let uu____16589 =
                                                names_to_string1 fvs2  in
                                              let uu____16591 =
                                                names_to_string1 fvs1  in
                                              let uu____16593 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16589 uu____16591
                                                uu____16593)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16605 ->
                          if wl.defer_ok
                          then
                            let uu____16609 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16609
                          else
                            (let uu____16614 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16614 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16640 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16640
                             | (FStar_Util.Inl msg,uu____16642) ->
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
                  let uu____16660 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16660
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16666 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16666
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16688 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16688
                else
                  (let uu____16693 =
                     let uu____16710 = quasi_pattern env lhs  in
                     let uu____16717 = quasi_pattern env rhs  in
                     (uu____16710, uu____16717)  in
                   match uu____16693 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16760 = lhs  in
                       (match uu____16760 with
                        | ({ FStar_Syntax_Syntax.n = uu____16761;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16763;_},u_lhs,uu____16765)
                            ->
                            let uu____16768 = rhs  in
                            (match uu____16768 with
                             | (uu____16769,u_rhs,uu____16771) ->
                                 let uu____16772 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16772
                                 then
                                   let uu____16779 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16779
                                 else
                                   (let uu____16782 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16782 with
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
                                        let uu____16814 =
                                          let uu____16821 =
                                            let uu____16824 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16824
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16821
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16814 with
                                         | (uu____16836,w,wl1) ->
                                             let w_app =
                                               let uu____16840 =
                                                 FStar_List.map
                                                   (fun uu____16851  ->
                                                      match uu____16851 with
                                                      | (z,uu____16859) ->
                                                          let uu____16864 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              z
                                                             in
                                                          FStar_Syntax_Syntax.as_arg
                                                            uu____16864) zs
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 w uu____16840
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16866 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16866
                                               then
                                                 let uu____16871 =
                                                   let uu____16875 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16877 =
                                                     let uu____16881 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16883 =
                                                       let uu____16887 =
                                                         term_to_string w  in
                                                       let uu____16889 =
                                                         let uu____16893 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16902 =
                                                           let uu____16906 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16915 =
                                                             let uu____16919
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16919]
                                                              in
                                                           uu____16906 ::
                                                             uu____16915
                                                            in
                                                         uu____16893 ::
                                                           uu____16902
                                                          in
                                                       uu____16887 ::
                                                         uu____16889
                                                        in
                                                     uu____16881 ::
                                                       uu____16883
                                                      in
                                                   uu____16875 :: uu____16877
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16871
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16936 =
                                                     let uu____16941 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16941)  in
                                                   TERM uu____16936  in
                                                 let uu____16942 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16942
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16950 =
                                                        let uu____16955 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16955)
                                                         in
                                                      TERM uu____16950  in
                                                    [s1; s2])
                                                  in
                                               let uu____16956 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16956))))))
                   | uu____16957 ->
                       let uu____16974 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16974)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17028 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____17028
            then
              let uu____17033 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17035 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17037 = FStar_Syntax_Print.term_to_string t2  in
              let uu____17039 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17033 uu____17035 uu____17037 uu____17039
            else ());
           (let uu____17050 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17050 with
            | (head1,args1) ->
                let uu____17093 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17093 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17163 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17163 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17168 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17168)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17189 =
                         mklstr
                           (fun uu____17200  ->
                              let uu____17201 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17203 = args_to_string args1  in
                              let uu____17207 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17209 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17201 uu____17203 uu____17207
                                uu____17209)
                          in
                       giveup env1 uu____17189 orig
                     else
                       (let uu____17216 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17221 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17221 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17216
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2533_17225 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2533_17225.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2533_17225.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2533_17225.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2533_17225.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2533_17225.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2533_17225.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2533_17225.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2533_17225.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17235 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17235
                                    else solve env1 wl2))
                        else
                          (let uu____17240 = base_and_refinement env1 t1  in
                           match uu____17240 with
                           | (base1,refinement1) ->
                               let uu____17265 = base_and_refinement env1 t2
                                  in
                               (match uu____17265 with
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
                                           let uu____17430 =
                                             FStar_List.fold_right
                                               (fun uu____17470  ->
                                                  fun uu____17471  ->
                                                    match (uu____17470,
                                                            uu____17471)
                                                    with
                                                    | (((a1,uu____17523),
                                                        (a2,uu____17525)),
                                                       (probs,wl3)) ->
                                                        let uu____17574 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17574
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17430 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17617 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17617
                                                 then
                                                   let uu____17622 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17622
                                                 else ());
                                                (let uu____17628 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17628
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
                                                    (let uu____17655 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17655 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17671 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17671
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17679 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17679))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17704 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17704 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17720 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17720
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17728 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17728)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17756 =
                                           match uu____17756 with
                                           | (prob,reason) ->
                                               ((let uu____17773 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17773
                                                 then
                                                   let uu____17778 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17780 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____17778 uu____17780
                                                 else ());
                                                (let uu____17786 =
                                                   let uu____17795 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17798 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17795, uu____17798)
                                                    in
                                                 match uu____17786 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17811 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17811 with
                                                      | (head1',uu____17829)
                                                          ->
                                                          let uu____17854 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17854
                                                           with
                                                           | (head2',uu____17872)
                                                               ->
                                                               let uu____17897
                                                                 =
                                                                 let uu____17902
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17903
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17902,
                                                                   uu____17903)
                                                                  in
                                                               (match uu____17897
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17905
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17905
                                                                    then
                                                                    let uu____17910
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17912
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17914
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17916
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17910
                                                                    uu____17912
                                                                    uu____17914
                                                                    uu____17916
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17921
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2621_17929
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2621_17929.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2621_17929.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2621_17929.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2621_17929.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2621_17929.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2621_17929.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2621_17929.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2621_17929.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17931
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17931
                                                                    then
                                                                    let uu____17936
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17936
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17941 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17953 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17953 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17961 =
                                             let uu____17962 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17962.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17961 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17967 -> false  in
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
                                          | uu____17970 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17973 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2641_18009 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2641_18009.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2641_18009.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2641_18009.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2641_18009.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2641_18009.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2641_18009.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2641_18009.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2641_18009.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18085 = destruct_flex_t scrutinee wl1  in
             match uu____18085 with
             | ((_t,uv,_args),wl2) ->
                 let uu____18096 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18096 with
                  | (xs,pat_term,uu____18112,uu____18113) ->
                      let uu____18118 =
                        FStar_List.fold_left
                          (fun uu____18141  ->
                             fun x  ->
                               match uu____18141 with
                               | (subst,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18162 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18162 with
                                    | (uu____18181,u,wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst  in
                                        (subst1, wl4))) ([], wl2) xs
                         in
                      (match uu____18118 with
                       | (subst,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term  in
                           let uu____18202 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18202 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2681_18219 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2681_18219.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2681_18219.umax_heuristic_ok);
                                    tcenv = (uu___2681_18219.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2681_18219.repr_subcomp_allowed)
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18230 = solve env1 wl'  in
                                (match uu____18230 with
                                 | Success (uu____18233,imps) ->
                                     let wl'1 =
                                       let uu___2689_18236 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2689_18236.wl_deferred);
                                         ctr = (uu___2689_18236.ctr);
                                         defer_ok =
                                           (uu___2689_18236.defer_ok);
                                         smt_ok = (uu___2689_18236.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2689_18236.umax_heuristic_ok);
                                         tcenv = (uu___2689_18236.tcenv);
                                         wl_implicits =
                                           (uu___2689_18236.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2689_18236.repr_subcomp_allowed)
                                       }  in
                                     let uu____18237 = solve env1 wl'1  in
                                     (match uu____18237 with
                                      | Success (uu____18240,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2697_18244 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2697_18244.attempting);
                                                 wl_deferred =
                                                   (uu___2697_18244.wl_deferred);
                                                 ctr = (uu___2697_18244.ctr);
                                                 defer_ok =
                                                   (uu___2697_18244.defer_ok);
                                                 smt_ok =
                                                   (uu___2697_18244.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2697_18244.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2697_18244.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'));
                                                 repr_subcomp_allowed =
                                                   (uu___2697_18244.repr_subcomp_allowed)
                                               })))
                                      | Failed uu____18245 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18251 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18274 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18274
                 then
                   let uu____18279 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18281 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18279 uu____18281
                 else ());
                (let uu____18286 =
                   let uu____18307 =
                     let uu____18316 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18316)  in
                   let uu____18323 =
                     let uu____18332 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18332)  in
                   (uu____18307, uu____18323)  in
                 match uu____18286 with
                 | ((uu____18362,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18365;
                                   FStar_Syntax_Syntax.vars = uu____18366;_}),
                    (s,t)) ->
                     let uu____18437 =
                       let uu____18439 = is_flex scrutinee  in
                       Prims.op_Negation uu____18439  in
                     if uu____18437
                     then
                       ((let uu____18450 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18450
                         then
                           let uu____18455 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18455
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18474 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18474
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18489 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18489
                           then
                             let uu____18494 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18496 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18494 uu____18496
                           else ());
                          (let pat_discriminates uu___26_18521 =
                             match uu___26_18521 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18537;
                                  FStar_Syntax_Syntax.p = uu____18538;_},FStar_Pervasives_Native.None
                                ,uu____18539) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18553;
                                  FStar_Syntax_Syntax.p = uu____18554;_},FStar_Pervasives_Native.None
                                ,uu____18555) -> true
                             | uu____18582 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18685 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18685 with
                                       | (uu____18687,uu____18688,t') ->
                                           let uu____18706 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18706 with
                                            | (FullMatch ,uu____18718) ->
                                                true
                                            | (HeadMatch
                                               uu____18732,uu____18733) ->
                                                true
                                            | uu____18748 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18785 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18785
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18796 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18796 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18884,uu____18885) ->
                                       branches1
                                   | uu____19030 -> branches  in
                                 let uu____19085 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19094 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19094 with
                                        | (p,uu____19098,uu____19099) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19128  ->
                                      FStar_Util.Inr uu____19128) uu____19085))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19158 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19158 with
                                | (p,uu____19167,e) ->
                                    ((let uu____19186 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19186
                                      then
                                        let uu____19191 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19193 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19191 uu____19193
                                      else ());
                                     (let uu____19198 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____19213  ->
                                           FStar_Util.Inr uu____19213)
                                        uu____19198)))))
                 | ((s,t),(uu____19216,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19219;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19220;_}))
                     ->
                     let uu____19289 =
                       let uu____19291 = is_flex scrutinee  in
                       Prims.op_Negation uu____19291  in
                     if uu____19289
                     then
                       ((let uu____19302 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19302
                         then
                           let uu____19307 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19307
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19326 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19326
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19341 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19341
                           then
                             let uu____19346 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19348 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19346 uu____19348
                           else ());
                          (let pat_discriminates uu___26_19373 =
                             match uu___26_19373 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19389;
                                  FStar_Syntax_Syntax.p = uu____19390;_},FStar_Pervasives_Native.None
                                ,uu____19391) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19405;
                                  FStar_Syntax_Syntax.p = uu____19406;_},FStar_Pervasives_Native.None
                                ,uu____19407) -> true
                             | uu____19434 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19537 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19537 with
                                       | (uu____19539,uu____19540,t') ->
                                           let uu____19558 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19558 with
                                            | (FullMatch ,uu____19570) ->
                                                true
                                            | (HeadMatch
                                               uu____19584,uu____19585) ->
                                                true
                                            | uu____19600 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19637 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19637
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19648 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19648 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19736,uu____19737) ->
                                       branches1
                                   | uu____19882 -> branches  in
                                 let uu____19937 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19946 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19946 with
                                        | (p,uu____19950,uu____19951) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19980  ->
                                      FStar_Util.Inr uu____19980) uu____19937))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20010 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20010 with
                                | (p,uu____20019,e) ->
                                    ((let uu____20038 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20038
                                      then
                                        let uu____20043 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20045 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20043 uu____20045
                                      else ());
                                     (let uu____20050 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____20065  ->
                                           FStar_Util.Inr uu____20065)
                                        uu____20050)))))
                 | uu____20066 ->
                     ((let uu____20088 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20088
                       then
                         let uu____20093 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20095 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20093 uu____20095
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20141 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20141
            then
              let uu____20146 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20148 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20150 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20152 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20146 uu____20148 uu____20150 uu____20152
            else ());
           (let uu____20157 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20157 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20188,uu____20189) ->
                     let rec may_relate head =
                       let uu____20217 =
                         let uu____20218 = FStar_Syntax_Subst.compress head
                            in
                         uu____20218.FStar_Syntax_Syntax.n  in
                       match uu____20217 with
                       | FStar_Syntax_Syntax.Tm_name uu____20222 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20224 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20249 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20249 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20251 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20254
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20255 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20258,uu____20259) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20301) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20307) ->
                           may_relate t
                       | uu____20312 -> false  in
                     let uu____20314 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20314 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20327 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20327
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20337 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20337
                          then
                            let uu____20340 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20340 with
                             | (guard,wl2) ->
                                 let uu____20347 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20347)
                          else
                            (let uu____20350 =
                               mklstr
                                 (fun uu____20361  ->
                                    let uu____20362 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20364 =
                                      let uu____20366 =
                                        let uu____20370 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20370
                                          (fun x  ->
                                             let uu____20377 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20377)
                                         in
                                      FStar_Util.dflt "" uu____20366  in
                                    let uu____20382 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20384 =
                                      let uu____20386 =
                                        let uu____20390 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20390
                                          (fun x  ->
                                             let uu____20397 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20397)
                                         in
                                      FStar_Util.dflt "" uu____20386  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20362 uu____20364 uu____20382
                                      uu____20384)
                                in
                             giveup env1 uu____20350 orig))
                 | (HeadMatch (true ),uu____20403) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20418 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20418 with
                        | (guard,wl2) ->
                            let uu____20425 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20425)
                     else
                       (let uu____20428 =
                          mklstr
                            (fun uu____20435  ->
                               let uu____20436 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20438 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20436 uu____20438)
                           in
                        giveup env1 uu____20428 orig)
                 | (uu____20441,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2872_20455 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2872_20455.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2872_20455.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2872_20455.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2872_20455.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2872_20455.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2872_20455.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2872_20455.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2872_20455.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20482 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20482
          then
            let uu____20485 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20485
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20491 =
                let uu____20494 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20494  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20491 t1);
             (let uu____20513 =
                let uu____20516 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20516  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20513 t2);
             (let uu____20535 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20535
              then
                let uu____20539 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20541 =
                  let uu____20543 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20545 =
                    let uu____20547 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20547  in
                  Prims.op_Hat uu____20543 uu____20545  in
                let uu____20550 =
                  let uu____20552 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20554 =
                    let uu____20556 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20556  in
                  Prims.op_Hat uu____20552 uu____20554  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20539 uu____20541 uu____20550
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20563,uu____20564) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20580,FStar_Syntax_Syntax.Tm_delayed uu____20581) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20597,uu____20598) ->
                  let uu____20625 =
                    let uu___2903_20626 = problem  in
                    let uu____20627 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2903_20626.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20627;
                      FStar_TypeChecker_Common.relation =
                        (uu___2903_20626.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2903_20626.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2903_20626.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2903_20626.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2903_20626.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2903_20626.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2903_20626.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2903_20626.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20625 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20628,uu____20629) ->
                  let uu____20636 =
                    let uu___2909_20637 = problem  in
                    let uu____20638 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2909_20637.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20638;
                      FStar_TypeChecker_Common.relation =
                        (uu___2909_20637.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2909_20637.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2909_20637.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2909_20637.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2909_20637.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2909_20637.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2909_20637.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2909_20637.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20636 wl
              | (uu____20639,FStar_Syntax_Syntax.Tm_ascribed uu____20640) ->
                  let uu____20667 =
                    let uu___2915_20668 = problem  in
                    let uu____20669 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2915_20668.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2915_20668.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2915_20668.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20669;
                      FStar_TypeChecker_Common.element =
                        (uu___2915_20668.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2915_20668.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2915_20668.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2915_20668.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2915_20668.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2915_20668.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20667 wl
              | (uu____20670,FStar_Syntax_Syntax.Tm_meta uu____20671) ->
                  let uu____20678 =
                    let uu___2921_20679 = problem  in
                    let uu____20680 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2921_20679.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2921_20679.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2921_20679.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20680;
                      FStar_TypeChecker_Common.element =
                        (uu___2921_20679.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2921_20679.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2921_20679.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2921_20679.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2921_20679.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2921_20679.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20678 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20682),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20684)) ->
                  let uu____20693 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20693
              | (FStar_Syntax_Syntax.Tm_bvar uu____20694,uu____20695) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20697,FStar_Syntax_Syntax.Tm_bvar uu____20698) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___27_20768 =
                    match uu___27_20768 with
                    | [] -> c
                    | bs ->
                        let uu____20796 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20796
                     in
                  let uu____20807 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20807 with
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
                                    let uu____20956 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20956
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
                  let mk_t t l uu___28_21045 =
                    match uu___28_21045 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21087 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21087 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst  ->
                                  let uu____21232 =
                                    FStar_Syntax_Subst.subst subst tbody11
                                     in
                                  let uu____21233 =
                                    FStar_Syntax_Subst.subst subst tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21232
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21233 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21235,uu____21236) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21267 -> true
                    | uu____21287 -> false  in
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
                      (let uu____21347 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3023_21355 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3023_21355.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3023_21355.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3023_21355.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3023_21355.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3023_21355.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3023_21355.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3023_21355.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3023_21355.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3023_21355.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3023_21355.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3023_21355.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3023_21355.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3023_21355.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3023_21355.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3023_21355.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3023_21355.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3023_21355.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3023_21355.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3023_21355.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3023_21355.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3023_21355.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3023_21355.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3023_21355.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3023_21355.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3023_21355.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3023_21355.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3023_21355.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3023_21355.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3023_21355.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3023_21355.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3023_21355.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3023_21355.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3023_21355.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3023_21355.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3023_21355.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3023_21355.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3023_21355.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3023_21355.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3023_21355.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3023_21355.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3023_21355.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3023_21355.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3023_21355.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21347 with
                       | (uu____21360,ty,uu____21362) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21371 =
                                 let uu____21372 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21372.FStar_Syntax_Syntax.n  in
                               match uu____21371 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21375 ->
                                   let uu____21382 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21382
                               | uu____21383 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21386 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21386
                             then
                               let uu____21391 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21393 =
                                 let uu____21395 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21395
                                  in
                               let uu____21396 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21391 uu____21393 uu____21396
                             else ());
                            r1))
                     in
                  let uu____21401 =
                    let uu____21418 = maybe_eta t1  in
                    let uu____21425 = maybe_eta t2  in
                    (uu____21418, uu____21425)  in
                  (match uu____21401 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3044_21467 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3044_21467.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3044_21467.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3044_21467.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3044_21467.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3044_21467.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3044_21467.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3044_21467.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3044_21467.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21488 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21488
                       then
                         let uu____21491 = destruct_flex_t not_abs wl  in
                         (match uu____21491 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3061_21508 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3061_21508.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3061_21508.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3061_21508.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3061_21508.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3061_21508.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3061_21508.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3061_21508.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3061_21508.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21511 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21511 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21534 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21534
                       then
                         let uu____21537 = destruct_flex_t not_abs wl  in
                         (match uu____21537 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3061_21554 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3061_21554.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3061_21554.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3061_21554.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3061_21554.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3061_21554.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3061_21554.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3061_21554.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3061_21554.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21557 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21557 orig))
                   | uu____21560 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21578,FStar_Syntax_Syntax.Tm_abs uu____21579) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21610 -> true
                    | uu____21630 -> false  in
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
                      (let uu____21690 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3023_21698 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3023_21698.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3023_21698.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3023_21698.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3023_21698.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3023_21698.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3023_21698.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3023_21698.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3023_21698.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3023_21698.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3023_21698.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3023_21698.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3023_21698.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3023_21698.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3023_21698.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3023_21698.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3023_21698.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3023_21698.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3023_21698.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3023_21698.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3023_21698.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3023_21698.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3023_21698.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3023_21698.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3023_21698.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3023_21698.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3023_21698.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3023_21698.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3023_21698.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3023_21698.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3023_21698.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3023_21698.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3023_21698.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3023_21698.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3023_21698.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3023_21698.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3023_21698.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3023_21698.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3023_21698.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3023_21698.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3023_21698.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3023_21698.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3023_21698.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3023_21698.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21690 with
                       | (uu____21703,ty,uu____21705) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21714 =
                                 let uu____21715 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21715.FStar_Syntax_Syntax.n  in
                               match uu____21714 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21718 ->
                                   let uu____21725 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21725
                               | uu____21726 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21729 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21729
                             then
                               let uu____21734 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21736 =
                                 let uu____21738 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21738
                                  in
                               let uu____21739 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21734 uu____21736 uu____21739
                             else ());
                            r1))
                     in
                  let uu____21744 =
                    let uu____21761 = maybe_eta t1  in
                    let uu____21768 = maybe_eta t2  in
                    (uu____21761, uu____21768)  in
                  (match uu____21744 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3044_21810 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3044_21810.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3044_21810.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3044_21810.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3044_21810.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3044_21810.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3044_21810.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3044_21810.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3044_21810.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21831 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21831
                       then
                         let uu____21834 = destruct_flex_t not_abs wl  in
                         (match uu____21834 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3061_21851 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3061_21851.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3061_21851.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3061_21851.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3061_21851.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3061_21851.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3061_21851.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3061_21851.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3061_21851.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21854 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21854 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21877 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21877
                       then
                         let uu____21880 = destruct_flex_t not_abs wl  in
                         (match uu____21880 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3061_21897 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3061_21897.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3061_21897.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3061_21897.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3061_21897.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3061_21897.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3061_21897.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3061_21897.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3061_21897.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21900 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21900 orig))
                   | uu____21903 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21933 =
                    let uu____21938 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21938 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3084_21966 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3084_21966.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3084_21966.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3086_21968 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3086_21968.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3086_21968.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21969,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3084_21984 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3084_21984.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3084_21984.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3086_21986 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3086_21986.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3086_21986.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21987 -> (x1, x2)  in
                  (match uu____21933 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____22006 = as_refinement false env t11  in
                       (match uu____22006 with
                        | (x12,phi11) ->
                            let uu____22014 = as_refinement false env t21  in
                            (match uu____22014 with
                             | (x22,phi21) ->
                                 ((let uu____22023 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22023
                                   then
                                     ((let uu____22028 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____22030 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22032 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22028
                                         uu____22030 uu____22032);
                                      (let uu____22035 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____22037 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22039 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22035
                                         uu____22037 uu____22039))
                                   else ());
                                  (let uu____22044 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____22044 with
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
                                         let uu____22115 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22115
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22127 =
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
                                         (let uu____22140 =
                                            let uu____22143 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22143
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22140
                                            (p_guard base_prob));
                                         (let uu____22162 =
                                            let uu____22165 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22165
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22162
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22184 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22184)
                                          in
                                       let has_uvars =
                                         (let uu____22189 =
                                            let uu____22191 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22191
                                             in
                                          Prims.op_Negation uu____22189) ||
                                           (let uu____22195 =
                                              let uu____22197 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22197
                                               in
                                            Prims.op_Negation uu____22195)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22201 =
                                           let uu____22206 =
                                             let uu____22215 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22215]  in
                                           mk_t_problem wl1 uu____22206 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22201 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22238 =
                                                solve env1
                                                  (let uu___3129_22240 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3129_22240.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3129_22240.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3129_22240.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3129_22240.tcenv);
                                                     wl_implicits =
                                                       (uu___3129_22240.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3129_22240.repr_subcomp_allowed)
                                                   })
                                                 in
                                              (match uu____22238 with
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
                                               | Success uu____22255 ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22264 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22264
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3142_22273 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3142_22273.attempting);
                                                         wl_deferred =
                                                           (uu___3142_22273.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3142_22273.defer_ok);
                                                         smt_ok =
                                                           (uu___3142_22273.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3142_22273.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3142_22273.tcenv);
                                                         wl_implicits =
                                                           (uu___3142_22273.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3142_22273.repr_subcomp_allowed)
                                                       }  in
                                                     let uu____22275 =
                                                       attempt [base_prob]
                                                         wl4
                                                        in
                                                     solve env1 uu____22275))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22278,FStar_Syntax_Syntax.Tm_uvar uu____22279) ->
                  let uu____22304 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22304 with
                   | (t11,wl1) ->
                       let uu____22311 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22311 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22320;
                    FStar_Syntax_Syntax.pos = uu____22321;
                    FStar_Syntax_Syntax.vars = uu____22322;_},uu____22323),FStar_Syntax_Syntax.Tm_uvar
                 uu____22324) ->
                  let uu____22373 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22373 with
                   | (t11,wl1) ->
                       let uu____22380 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22380 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22389,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22390;
                    FStar_Syntax_Syntax.pos = uu____22391;
                    FStar_Syntax_Syntax.vars = uu____22392;_},uu____22393))
                  ->
                  let uu____22442 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22442 with
                   | (t11,wl1) ->
                       let uu____22449 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22449 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22458;
                    FStar_Syntax_Syntax.pos = uu____22459;
                    FStar_Syntax_Syntax.vars = uu____22460;_},uu____22461),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22462;
                    FStar_Syntax_Syntax.pos = uu____22463;
                    FStar_Syntax_Syntax.vars = uu____22464;_},uu____22465))
                  ->
                  let uu____22538 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22538 with
                   | (t11,wl1) ->
                       let uu____22545 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22545 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22554,uu____22555) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22568 = destruct_flex_t t1 wl  in
                  (match uu____22568 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22575;
                    FStar_Syntax_Syntax.pos = uu____22576;
                    FStar_Syntax_Syntax.vars = uu____22577;_},uu____22578),uu____22579)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22616 = destruct_flex_t t1 wl  in
                  (match uu____22616 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22623,FStar_Syntax_Syntax.Tm_uvar uu____22624) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22637,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22638;
                    FStar_Syntax_Syntax.pos = uu____22639;
                    FStar_Syntax_Syntax.vars = uu____22640;_},uu____22641))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22678,FStar_Syntax_Syntax.Tm_arrow uu____22679) ->
                  solve_t' env
                    (let uu___3244_22707 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3244_22707.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3244_22707.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3244_22707.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3244_22707.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3244_22707.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3244_22707.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3244_22707.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3244_22707.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3244_22707.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22708;
                    FStar_Syntax_Syntax.pos = uu____22709;
                    FStar_Syntax_Syntax.vars = uu____22710;_},uu____22711),FStar_Syntax_Syntax.Tm_arrow
                 uu____22712) ->
                  solve_t' env
                    (let uu___3244_22764 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3244_22764.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3244_22764.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3244_22764.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3244_22764.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3244_22764.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3244_22764.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3244_22764.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3244_22764.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3244_22764.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22765,FStar_Syntax_Syntax.Tm_uvar uu____22766) ->
                  let uu____22779 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22779
              | (uu____22780,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22781;
                    FStar_Syntax_Syntax.pos = uu____22782;
                    FStar_Syntax_Syntax.vars = uu____22783;_},uu____22784))
                  ->
                  let uu____22821 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22821
              | (FStar_Syntax_Syntax.Tm_uvar uu____22822,uu____22823) ->
                  let uu____22836 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22836
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22837;
                    FStar_Syntax_Syntax.pos = uu____22838;
                    FStar_Syntax_Syntax.vars = uu____22839;_},uu____22840),uu____22841)
                  ->
                  let uu____22878 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22878
              | (FStar_Syntax_Syntax.Tm_refine uu____22879,uu____22880) ->
                  let t21 =
                    let uu____22888 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22888  in
                  solve_t env
                    (let uu___3279_22914 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3279_22914.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3279_22914.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3279_22914.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3279_22914.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3279_22914.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3279_22914.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3279_22914.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3279_22914.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3279_22914.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22915,FStar_Syntax_Syntax.Tm_refine uu____22916) ->
                  let t11 =
                    let uu____22924 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22924  in
                  solve_t env
                    (let uu___3286_22950 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3286_22950.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3286_22950.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3286_22950.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3286_22950.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3286_22950.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3286_22950.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3286_22950.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3286_22950.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3286_22950.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____23032 =
                    let uu____23033 = guard_of_prob env wl problem t1 t2  in
                    match uu____23033 with
                    | (guard,wl1) ->
                        let uu____23040 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____23040
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23259 = br1  in
                        (match uu____23259 with
                         | (p1,w1,uu____23288) ->
                             let uu____23305 = br2  in
                             (match uu____23305 with
                              | (p2,w2,uu____23328) ->
                                  let uu____23333 =
                                    let uu____23335 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23335  in
                                  if uu____23333
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23362 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23362 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23399 = br2  in
                                         (match uu____23399 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23432 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23432
                                                 in
                                              let uu____23437 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23468,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23489) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23548 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23548 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23437
                                                (fun uu____23620  ->
                                                   match uu____23620 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23657 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23657
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23678
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23678
                                                              then
                                                                let uu____23683
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23685
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23683
                                                                  uu____23685
                                                              else ());
                                                             (let uu____23691
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23691
                                                                (fun
                                                                   uu____23727
                                                                    ->
                                                                   match uu____23727
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
                    | uu____23856 -> FStar_Pervasives_Native.None  in
                  let uu____23897 = solve_branches wl brs1 brs2  in
                  (match uu____23897 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23923 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23923 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23950 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23950 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23984 =
                                FStar_List.map
                                  (fun uu____23996  ->
                                     match uu____23996 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23984  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____24005 =
                              let uu____24006 =
                                let uu____24007 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____24007
                                  (let uu___3385_24015 = wl3  in
                                   {
                                     attempting =
                                       (uu___3385_24015.attempting);
                                     wl_deferred =
                                       (uu___3385_24015.wl_deferred);
                                     ctr = (uu___3385_24015.ctr);
                                     defer_ok = (uu___3385_24015.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3385_24015.umax_heuristic_ok);
                                     tcenv = (uu___3385_24015.tcenv);
                                     wl_implicits =
                                       (uu___3385_24015.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3385_24015.repr_subcomp_allowed)
                                   })
                                 in
                              solve env uu____24006  in
                            (match uu____24005 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____24020 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24029 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____24029 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24032,uu____24033) ->
                  let head1 =
                    let uu____24057 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24057
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24103 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24103
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24149 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24149
                    then
                      let uu____24153 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24155 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24157 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24153 uu____24155 uu____24157
                    else ());
                   (let no_free_uvars t =
                      (let uu____24171 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24171) &&
                        (let uu____24175 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24175)
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
                      let uu____24194 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24194 = FStar_Syntax_Util.Equal  in
                    let uu____24195 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24195
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24199 = equal t1 t2  in
                         (if uu____24199
                          then
                            let uu____24202 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24202
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24207 =
                            let uu____24214 = equal t1 t2  in
                            if uu____24214
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24227 = mk_eq2 wl env orig t1 t2  in
                               match uu____24227 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24207 with
                          | (guard,wl1) ->
                              let uu____24248 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24248))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24251,uu____24252) ->
                  let head1 =
                    let uu____24260 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24260
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24306 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24306
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24352 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24352
                    then
                      let uu____24356 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24358 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24360 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24356 uu____24358 uu____24360
                    else ());
                   (let no_free_uvars t =
                      (let uu____24374 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24374) &&
                        (let uu____24378 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24378)
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
                      let uu____24397 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24397 = FStar_Syntax_Util.Equal  in
                    let uu____24398 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24398
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24402 = equal t1 t2  in
                         (if uu____24402
                          then
                            let uu____24405 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24405
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24410 =
                            let uu____24417 = equal t1 t2  in
                            if uu____24417
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24430 = mk_eq2 wl env orig t1 t2  in
                               match uu____24430 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24410 with
                          | (guard,wl1) ->
                              let uu____24451 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24451))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24454,uu____24455) ->
                  let head1 =
                    let uu____24457 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24457
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24503 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24503
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24549 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24549
                    then
                      let uu____24553 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24555 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24557 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24553 uu____24555 uu____24557
                    else ());
                   (let no_free_uvars t =
                      (let uu____24571 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24571) &&
                        (let uu____24575 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24575)
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
                      let uu____24594 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24594 = FStar_Syntax_Util.Equal  in
                    let uu____24595 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24595
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24599 = equal t1 t2  in
                         (if uu____24599
                          then
                            let uu____24602 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24602
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24607 =
                            let uu____24614 = equal t1 t2  in
                            if uu____24614
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24627 = mk_eq2 wl env orig t1 t2  in
                               match uu____24627 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24607 with
                          | (guard,wl1) ->
                              let uu____24648 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24648))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24651,uu____24652) ->
                  let head1 =
                    let uu____24654 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24654
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24700 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24700
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24746 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24746
                    then
                      let uu____24750 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24752 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24754 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24750 uu____24752 uu____24754
                    else ());
                   (let no_free_uvars t =
                      (let uu____24768 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24768) &&
                        (let uu____24772 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24772)
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
                      let uu____24791 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24791 = FStar_Syntax_Util.Equal  in
                    let uu____24792 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24792
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24796 = equal t1 t2  in
                         (if uu____24796
                          then
                            let uu____24799 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24799
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24804 =
                            let uu____24811 = equal t1 t2  in
                            if uu____24811
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24824 = mk_eq2 wl env orig t1 t2  in
                               match uu____24824 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24804 with
                          | (guard,wl1) ->
                              let uu____24845 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24845))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24848,uu____24849) ->
                  let head1 =
                    let uu____24851 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24851
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24897 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24897
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24943 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24943
                    then
                      let uu____24947 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24949 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24951 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24947 uu____24949 uu____24951
                    else ());
                   (let no_free_uvars t =
                      (let uu____24965 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24965) &&
                        (let uu____24969 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24969)
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
                      let uu____24988 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24988 = FStar_Syntax_Util.Equal  in
                    let uu____24989 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24989
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24993 = equal t1 t2  in
                         (if uu____24993
                          then
                            let uu____24996 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24996
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25001 =
                            let uu____25008 = equal t1 t2  in
                            if uu____25008
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25021 = mk_eq2 wl env orig t1 t2  in
                               match uu____25021 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25001 with
                          | (guard,wl1) ->
                              let uu____25042 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25042))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25045,uu____25046) ->
                  let head1 =
                    let uu____25064 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25064
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25110 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25110
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25156 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25156
                    then
                      let uu____25160 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25162 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25164 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25160 uu____25162 uu____25164
                    else ());
                   (let no_free_uvars t =
                      (let uu____25178 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25178) &&
                        (let uu____25182 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25182)
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
                      let uu____25201 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25201 = FStar_Syntax_Util.Equal  in
                    let uu____25202 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25202
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25206 = equal t1 t2  in
                         (if uu____25206
                          then
                            let uu____25209 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25209
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25214 =
                            let uu____25221 = equal t1 t2  in
                            if uu____25221
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25234 = mk_eq2 wl env orig t1 t2  in
                               match uu____25234 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25214 with
                          | (guard,wl1) ->
                              let uu____25255 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25255))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25258,FStar_Syntax_Syntax.Tm_match uu____25259) ->
                  let head1 =
                    let uu____25283 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25283
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25329 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25329
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25375 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25375
                    then
                      let uu____25379 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25381 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25383 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25379 uu____25381 uu____25383
                    else ());
                   (let no_free_uvars t =
                      (let uu____25397 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25397) &&
                        (let uu____25401 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25401)
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
                      let uu____25420 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25420 = FStar_Syntax_Util.Equal  in
                    let uu____25421 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25421
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25425 = equal t1 t2  in
                         (if uu____25425
                          then
                            let uu____25428 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25428
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25433 =
                            let uu____25440 = equal t1 t2  in
                            if uu____25440
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25453 = mk_eq2 wl env orig t1 t2  in
                               match uu____25453 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25433 with
                          | (guard,wl1) ->
                              let uu____25474 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25474))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25477,FStar_Syntax_Syntax.Tm_uinst uu____25478) ->
                  let head1 =
                    let uu____25486 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25486
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25532 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25532
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25578 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25578
                    then
                      let uu____25582 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25584 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25586 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25582 uu____25584 uu____25586
                    else ());
                   (let no_free_uvars t =
                      (let uu____25600 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25600) &&
                        (let uu____25604 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25604)
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
                      let uu____25623 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25623 = FStar_Syntax_Util.Equal  in
                    let uu____25624 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25624
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25628 = equal t1 t2  in
                         (if uu____25628
                          then
                            let uu____25631 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25631
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25636 =
                            let uu____25643 = equal t1 t2  in
                            if uu____25643
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25656 = mk_eq2 wl env orig t1 t2  in
                               match uu____25656 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25636 with
                          | (guard,wl1) ->
                              let uu____25677 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25677))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25680,FStar_Syntax_Syntax.Tm_name uu____25681) ->
                  let head1 =
                    let uu____25683 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25683
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25729 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25729
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25769 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25769
                    then
                      let uu____25773 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25775 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25777 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25773 uu____25775 uu____25777
                    else ());
                   (let no_free_uvars t =
                      (let uu____25791 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25791) &&
                        (let uu____25795 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25795)
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
                      let uu____25814 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25814 = FStar_Syntax_Util.Equal  in
                    let uu____25815 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25815
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25819 = equal t1 t2  in
                         (if uu____25819
                          then
                            let uu____25822 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25822
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25827 =
                            let uu____25834 = equal t1 t2  in
                            if uu____25834
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25847 = mk_eq2 wl env orig t1 t2  in
                               match uu____25847 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25827 with
                          | (guard,wl1) ->
                              let uu____25868 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25868))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25871,FStar_Syntax_Syntax.Tm_constant uu____25872) ->
                  let head1 =
                    let uu____25874 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25874
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25914 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25914
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25954 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25954
                    then
                      let uu____25958 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25960 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25962 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25958 uu____25960 uu____25962
                    else ());
                   (let no_free_uvars t =
                      (let uu____25976 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25976) &&
                        (let uu____25980 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25980)
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
                      let uu____25999 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25999 = FStar_Syntax_Util.Equal  in
                    let uu____26000 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26000
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26004 = equal t1 t2  in
                         (if uu____26004
                          then
                            let uu____26007 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26007
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26012 =
                            let uu____26019 = equal t1 t2  in
                            if uu____26019
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26032 = mk_eq2 wl env orig t1 t2  in
                               match uu____26032 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26012 with
                          | (guard,wl1) ->
                              let uu____26053 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26053))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26056,FStar_Syntax_Syntax.Tm_fvar uu____26057) ->
                  let head1 =
                    let uu____26059 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26059
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26105 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26105
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26151 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26151
                    then
                      let uu____26155 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26157 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26159 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26155 uu____26157 uu____26159
                    else ());
                   (let no_free_uvars t =
                      (let uu____26173 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26173) &&
                        (let uu____26177 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26177)
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
                      let uu____26196 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26196 = FStar_Syntax_Util.Equal  in
                    let uu____26197 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26197
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26201 = equal t1 t2  in
                         (if uu____26201
                          then
                            let uu____26204 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26204
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26209 =
                            let uu____26216 = equal t1 t2  in
                            if uu____26216
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26229 = mk_eq2 wl env orig t1 t2  in
                               match uu____26229 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26209 with
                          | (guard,wl1) ->
                              let uu____26250 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26250))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26253,FStar_Syntax_Syntax.Tm_app uu____26254) ->
                  let head1 =
                    let uu____26272 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26272
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26312 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26312
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26352 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26352
                    then
                      let uu____26356 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26358 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26360 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26356 uu____26358 uu____26360
                    else ());
                   (let no_free_uvars t =
                      (let uu____26374 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26374) &&
                        (let uu____26378 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26378)
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
                      let uu____26397 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26397 = FStar_Syntax_Util.Equal  in
                    let uu____26398 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26398
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26402 = equal t1 t2  in
                         (if uu____26402
                          then
                            let uu____26405 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26405
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26410 =
                            let uu____26417 = equal t1 t2  in
                            if uu____26417
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26430 = mk_eq2 wl env orig t1 t2  in
                               match uu____26430 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26410 with
                          | (guard,wl1) ->
                              let uu____26451 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26451))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26454,FStar_Syntax_Syntax.Tm_let uu____26455) ->
                  let uu____26482 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26482
                  then
                    let uu____26485 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26485
                  else
                    (let uu____26488 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26488 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26491,uu____26492) ->
                  let uu____26506 =
                    let uu____26512 =
                      let uu____26514 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26516 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26518 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26520 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26514 uu____26516 uu____26518 uu____26520
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26512)
                     in
                  FStar_Errors.raise_error uu____26506
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26524,FStar_Syntax_Syntax.Tm_let uu____26525) ->
                  let uu____26539 =
                    let uu____26545 =
                      let uu____26547 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26549 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26551 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26553 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26547 uu____26549 uu____26551 uu____26553
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26545)
                     in
                  FStar_Errors.raise_error uu____26539
                    t1.FStar_Syntax_Syntax.pos
              | uu____26557 ->
                  let uu____26562 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26562 orig))))

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
          (let uu____26628 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26628
           then
             let uu____26633 =
               let uu____26635 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26635  in
             let uu____26636 =
               let uu____26638 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26638  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26633 uu____26636
           else ());
          (let uu____26642 =
             let uu____26644 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26644  in
           if uu____26642
           then
             let uu____26647 =
               mklstr
                 (fun uu____26654  ->
                    let uu____26655 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26657 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26655 uu____26657)
                in
             giveup env uu____26647 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26679 =
                  mklstr
                    (fun uu____26686  ->
                       let uu____26687 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26689 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26687 uu____26689)
                   in
                giveup env uu____26679 orig)
             else
               (let uu____26694 =
                  FStar_List.fold_left2
                    (fun uu____26715  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26715 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26736 =
                                 let uu____26741 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26742 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26741
                                   FStar_TypeChecker_Common.EQ uu____26742
                                   "effect universes"
                                  in
                               (match uu____26736 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26694 with
                | (univ_sub_probs,wl1) ->
                    let uu____26762 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26762 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26770 =
                           FStar_List.fold_right2
                             (fun uu____26807  ->
                                fun uu____26808  ->
                                  fun uu____26809  ->
                                    match (uu____26807, uu____26808,
                                            uu____26809)
                                    with
                                    | ((a1,uu____26853),(a2,uu____26855),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26888 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26888 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26770 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26915 =
                                  let uu____26918 =
                                    let uu____26921 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26921
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26918
                                   in
                                FStar_List.append univ_sub_probs uu____26915
                                 in
                              let guard =
                                let guard =
                                  let uu____26943 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26943  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3537_26952 = wl3  in
                                {
                                  attempting = (uu___3537_26952.attempting);
                                  wl_deferred = (uu___3537_26952.wl_deferred);
                                  ctr = (uu___3537_26952.ctr);
                                  defer_ok = (uu___3537_26952.defer_ok);
                                  smt_ok = (uu___3537_26952.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3537_26952.umax_heuristic_ok);
                                  tcenv = (uu___3537_26952.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3537_26952.repr_subcomp_allowed)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26954 = attempt sub_probs wl5  in
                              solve env uu____26954))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26972 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26972
           then
             let uu____26977 =
               let uu____26979 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26979
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26981 =
               let uu____26983 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26983
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26977 uu____26981
           else ());
          (let uu____26988 =
             let uu____26993 =
               let uu____26998 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26998
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26993
               (fun uu____27015  ->
                  match uu____27015 with
                  | (c,g) ->
                      let uu____27026 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____27026, g))
              in
           match uu____26988 with
           | (c12,g_lift) ->
               ((let uu____27030 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____27030
                 then
                   let uu____27035 =
                     let uu____27037 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27037
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____27039 =
                     let uu____27041 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27041
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____27035 uu____27039
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3557_27051 = wl  in
                     {
                       attempting = (uu___3557_27051.attempting);
                       wl_deferred = (uu___3557_27051.wl_deferred);
                       ctr = (uu___3557_27051.ctr);
                       defer_ok = (uu___3557_27051.defer_ok);
                       smt_ok = (uu___3557_27051.smt_ok);
                       umax_heuristic_ok =
                         (uu___3557_27051.umax_heuristic_ok);
                       tcenv = (uu___3557_27051.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits);
                       repr_subcomp_allowed =
                         (uu___3557_27051.repr_subcomp_allowed)
                     }  in
                   let uu____27052 =
                     let rec is_uvar t =
                       let uu____27066 =
                         let uu____27067 = FStar_Syntax_Subst.compress t  in
                         uu____27067.FStar_Syntax_Syntax.n  in
                       match uu____27066 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____27071 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27086) ->
                           is_uvar t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27092) ->
                           is_uvar t1
                       | uu____27117 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27151  ->
                          fun uu____27152  ->
                            fun uu____27153  ->
                              match (uu____27151, uu____27152, uu____27153)
                              with
                              | ((a1,uu____27197),(a2,uu____27199),(is_sub_probs,wl2))
                                  ->
                                  let uu____27232 = is_uvar a1  in
                                  if uu____27232
                                  then
                                    ((let uu____27242 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27242
                                      then
                                        let uu____27247 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27249 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27247 uu____27249
                                      else ());
                                     (let uu____27254 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27254 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____27052 with
                   | (is_sub_probs,wl2) ->
                       let uu____27282 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27282 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27290 =
                              let uu____27295 =
                                let uu____27296 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27296
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27295
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27290 with
                             | (uu____27303,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27314 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27316 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27314 s uu____27316
                                    in
                                 let uu____27319 =
                                   let uu____27348 =
                                     let uu____27349 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27349.FStar_Syntax_Syntax.n  in
                                   match uu____27348 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27409 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27409 with
                                        | (bs',c3) ->
                                            let a = FStar_List.hd bs'  in
                                            let bs1 = FStar_List.tail bs'  in
                                            let uu____27472 =
                                              let uu____27491 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27491
                                                (fun uu____27595  ->
                                                   match uu____27595 with
                                                   | (l1,l2) ->
                                                       let uu____27668 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27668))
                                               in
                                            (match uu____27472 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27773 ->
                                       let uu____27774 =
                                         let uu____27780 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27780)
                                          in
                                       FStar_Errors.raise_error uu____27774 r
                                    in
                                 (match uu____27319 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27856 =
                                        let uu____27863 =
                                          let uu____27864 =
                                            let uu____27865 =
                                              let uu____27872 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27872,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27865
                                             in
                                          [uu____27864]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27863
                                          (fun b  ->
                                             let uu____27888 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27890 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27892 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27888 uu____27890
                                               uu____27892) r
                                         in
                                      (match uu____27856 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27902 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27902
                                             then
                                               let uu____27907 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27916 =
                                                          let uu____27918 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27918
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27916) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27907
                                             else ());
                                            (let wl4 =
                                               let uu___3629_27926 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3629_27926.attempting);
                                                 wl_deferred =
                                                   (uu___3629_27926.wl_deferred);
                                                 ctr = (uu___3629_27926.ctr);
                                                 defer_ok =
                                                   (uu___3629_27926.defer_ok);
                                                 smt_ok =
                                                   (uu___3629_27926.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3629_27926.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3629_27926.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits);
                                                 repr_subcomp_allowed =
                                                   (uu___3629_27926.repr_subcomp_allowed)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27951 =
                                                        let uu____27958 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27958, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27951) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27975 =
                                               let f_sort_is =
                                                 let uu____27985 =
                                                   let uu____27986 =
                                                     let uu____27989 =
                                                       let uu____27990 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27990.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27989
                                                      in
                                                   uu____27986.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27985 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____28001,uu____28002::is)
                                                     ->
                                                     let uu____28044 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____28044
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28077 ->
                                                     let uu____28078 =
                                                       let uu____28084 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28084)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28078 r
                                                  in
                                               let uu____28090 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28125  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28125
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28146 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28146
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28090
                                                in
                                             match uu____27975 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28171 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28171
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28172 =
                                                   let g_sort_is =
                                                     let uu____28182 =
                                                       let uu____28183 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28183.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28182 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28188,uu____28189::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28249 ->
                                                         let uu____28250 =
                                                           let uu____28256 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28256)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28250 r
                                                      in
                                                   let uu____28262 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28297  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28297
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28318
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28318
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28262
                                                    in
                                                 (match uu____28172 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28345 =
                                                          let uu____28350 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28351 =
                                                            let uu____28352 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28352
                                                             in
                                                          (uu____28350,
                                                            uu____28351)
                                                           in
                                                        match uu____28345
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28380 =
                                                          let uu____28383 =
                                                            let uu____28386 =
                                                              let uu____28389
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28389
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28386
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28383
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28380
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28413 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28413
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
                                                        let uu____28424 =
                                                          let uu____28427 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun uu____28430 
                                                               ->
                                                               FStar_Pervasives_Native.Some
                                                                 uu____28430)
                                                            uu____28427
                                                           in
                                                        solve_prob orig
                                                          uu____28424 [] wl6
                                                         in
                                                      let uu____28431 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28431))))))))))
           in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env  in
           let lift_c1 uu____28459 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____28461 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ
                      in
                   [uu____28461]
               | x -> x  in
             let c12 =
               let uu___3697_28464 = c11  in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3697_28464.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3697_28464.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3697_28464.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3697_28464.FStar_Syntax_Syntax.flags)
               }  in
             let uu____28465 =
               let uu____28470 =
                 FStar_All.pipe_right
                   (let uu___3700_28472 = c12  in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3700_28472.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3700_28472.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3700_28472.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3700_28472.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____28470
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____28465
               (fun uu____28486  ->
                  match uu____28486 with
                  | (c,g) ->
                      let uu____28493 =
                        let uu____28495 = FStar_TypeChecker_Env.is_trivial g
                           in
                        Prims.op_Negation uu____28495  in
                      if uu____28493
                      then
                        let uu____28498 =
                          let uu____28504 =
                            let uu____28506 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name
                               in
                            let uu____28508 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name
                               in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____28506 uu____28508
                             in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____28504)
                           in
                        FStar_Errors.raise_error uu____28498 r
                      else FStar_Syntax_Util.comp_to_comp_typ c)
              in
           let uu____28514 =
             FStar_TypeChecker_Env.is_layered_effect env
               c21.FStar_Syntax_Syntax.effect_name
              in
           if uu____28514
           then solve_layered_sub c11 edge c21
           else
             (let uu____28519 =
                ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                   (let uu____28522 =
                      FStar_Ident.lid_equals
                        c11.FStar_Syntax_Syntax.effect_name
                        c21.FStar_Syntax_Syntax.effect_name
                       in
                    Prims.op_Negation uu____28522))
                  &&
                  (FStar_TypeChecker_Env.is_reifiable_effect env
                     c21.FStar_Syntax_Syntax.effect_name)
                 in
              if uu____28519
              then
                let uu____28525 =
                  mklstr
                    (fun uu____28532  ->
                       let uu____28533 =
                         FStar_Ident.string_of_lid
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____28535 =
                         FStar_Ident.string_of_lid
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Cannot lift from %s to %s, it needs a lift\n"
                         uu____28533 uu____28535)
                   in
                giveup env uu____28525 orig
              else
                (let is_null_wp_2 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___29_28546  ->
                           match uu___29_28546 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | FStar_Syntax_Syntax.MLEFFECT  -> true
                           | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                           | uu____28551 -> false))
                    in
                 let uu____28553 =
                   match ((c11.FStar_Syntax_Syntax.effect_args),
                           (c21.FStar_Syntax_Syntax.effect_args))
                   with
                   | ((wp1,uu____28583)::uu____28584,(wp2,uu____28586)::uu____28587)
                       -> (wp1, wp2)
                   | uu____28660 ->
                       let uu____28685 =
                         let uu____28691 =
                           let uu____28693 =
                             FStar_Syntax_Print.lid_to_string
                               c11.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28695 =
                             FStar_Syntax_Print.lid_to_string
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Got effects %s and %s, expected normalized effects"
                             uu____28693 uu____28695
                            in
                         (FStar_Errors.Fatal_ExpectNormalizedEffect,
                           uu____28691)
                          in
                       FStar_Errors.raise_error uu____28685
                         env.FStar_TypeChecker_Env.range
                    in
                 match uu____28553 with
                 | (wpc1,wpc2) ->
                     let uu____28705 = FStar_Util.physical_equality wpc1 wpc2
                        in
                     if uu____28705
                     then
                       let uu____28708 =
                         problem_using_guard orig
                           c11.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____28708 wl
                     else
                       (let uu____28712 =
                          let uu____28719 =
                            FStar_TypeChecker_Env.effect_decl_opt env
                              c21.FStar_Syntax_Syntax.effect_name
                             in
                          FStar_Util.must uu____28719  in
                        match uu____28712 with
                        | (c2_decl,qualifiers) ->
                            let uu____28740 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            if uu____28740
                            then
                              let c1_repr =
                                let uu____28747 =
                                  let uu____28748 =
                                    let uu____28749 = lift_c1 ()  in
                                    FStar_Syntax_Syntax.mk_Comp uu____28749
                                     in
                                  let uu____28750 =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  FStar_TypeChecker_Env.reify_comp env
                                    uu____28748 uu____28750
                                   in
                                norm_with_steps
                                  "FStar.TypeChecker.Rel.norm_with_steps.4"
                                  [FStar_TypeChecker_Env.UnfoldUntil
                                     FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Env.Weak;
                                  FStar_TypeChecker_Env.HNF] env uu____28747
                                 in
                              let c2_repr =
                                let uu____28753 =
                                  let uu____28754 =
                                    FStar_Syntax_Syntax.mk_Comp c21  in
                                  let uu____28755 =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  FStar_TypeChecker_Env.reify_comp env
                                    uu____28754 uu____28755
                                   in
                                norm_with_steps
                                  "FStar.TypeChecker.Rel.norm_with_steps.5"
                                  [FStar_TypeChecker_Env.UnfoldUntil
                                     FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Env.Weak;
                                  FStar_TypeChecker_Env.HNF] env uu____28753
                                 in
                              let uu____28757 =
                                let uu____28762 =
                                  let uu____28764 =
                                    FStar_Syntax_Print.term_to_string c1_repr
                                     in
                                  let uu____28766 =
                                    FStar_Syntax_Print.term_to_string c2_repr
                                     in
                                  FStar_Util.format2
                                    "sub effect repr: %s <: %s" uu____28764
                                    uu____28766
                                   in
                                sub_prob wl c1_repr
                                  problem.FStar_TypeChecker_Common.relation
                                  c2_repr uu____28762
                                 in
                              (match uu____28757 with
                               | (prob,wl1) ->
                                   let wl2 =
                                     solve_prob orig
                                       (FStar_Pervasives_Native.Some
                                          (p_guard prob)) [] wl1
                                      in
                                   let uu____28772 = attempt [prob] wl2  in
                                   solve env uu____28772)
                            else
                              (let g =
                                 if env.FStar_TypeChecker_Env.lax
                                 then FStar_Syntax_Util.t_true
                                 else
                                   (let wpc1_2 =
                                      let uu____28792 = lift_c1 ()  in
                                      FStar_All.pipe_right uu____28792
                                        (fun ct  ->
                                           FStar_List.hd
                                             ct.FStar_Syntax_Syntax.effect_args)
                                       in
                                    if is_null_wp_2
                                    then
                                      ((let uu____28815 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other "Rel")
                                           in
                                        if uu____28815
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
                                          let uu____28825 =
                                            FStar_All.pipe_right c2_decl
                                              FStar_Syntax_Util.get_wp_trivial_combinator
                                             in
                                          match uu____28825 with
                                          | FStar_Pervasives_Native.None  ->
                                              failwith
                                                "Rel doesn't yet handle undefined trivial combinator in an effect"
                                          | FStar_Pervasives_Native.Some t ->
                                              t
                                           in
                                        let uu____28832 =
                                          let uu____28833 =
                                            let uu____28850 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28853 =
                                              let uu____28864 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28864; wpc1_2]  in
                                            (uu____28850, uu____28853)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28833
                                           in
                                        FStar_Syntax_Syntax.mk uu____28832 r))
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
                                       let uu____28913 =
                                         let uu____28914 =
                                           let uu____28931 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28934 =
                                             let uu____28945 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28954 =
                                               let uu____28965 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28965; wpc1_2]  in
                                             uu____28945 :: uu____28954  in
                                           (uu____28931, uu____28934)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28914
                                          in
                                       FStar_Syntax_Syntax.mk uu____28913 r))
                                  in
                               (let uu____29019 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____29019
                                then
                                  let uu____29024 =
                                    let uu____29026 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Iota;
                                        FStar_TypeChecker_Env.Eager_unfolding;
                                        FStar_TypeChecker_Env.Primops;
                                        FStar_TypeChecker_Env.Simplify] env g
                                       in
                                    FStar_Syntax_Print.term_to_string
                                      uu____29026
                                     in
                                  FStar_Util.print1
                                    "WP guard (simplifed) is (%s)\n"
                                    uu____29024
                                else ());
                               (let uu____29030 =
                                  sub_prob wl
                                    c11.FStar_Syntax_Syntax.result_typ
                                    problem.FStar_TypeChecker_Common.relation
                                    c21.FStar_Syntax_Syntax.result_typ
                                    "result type"
                                   in
                                match uu____29030 with
                                | (base_prob,wl1) ->
                                    let wl2 =
                                      let uu____29039 =
                                        let uu____29042 =
                                          FStar_Syntax_Util.mk_conj
                                            (p_guard base_prob) g
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____29045  ->
                                             FStar_Pervasives_Native.Some
                                               uu____29045) uu____29042
                                         in
                                      solve_prob orig uu____29039 [] wl1  in
                                    let uu____29046 = attempt [base_prob] wl2
                                       in
                                    solve env uu____29046))))))
           in
        let uu____29047 = FStar_Util.physical_equality c1 c2  in
        if uu____29047
        then
          let uu____29050 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____29050
        else
          ((let uu____29054 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____29054
            then
              let uu____29059 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____29061 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29059
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29061
            else ());
           (let uu____29066 =
              let uu____29075 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29078 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29075, uu____29078)  in
            match uu____29066 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29096),FStar_Syntax_Syntax.Total
                    (t2,uu____29098)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29115 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29115 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29117,FStar_Syntax_Syntax.Total uu____29118) ->
                     let uu____29135 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29135 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29139),FStar_Syntax_Syntax.Total
                    (t2,uu____29141)) ->
                     let uu____29158 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29158 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29161),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29163)) ->
                     let uu____29180 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29180 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29183),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29185)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29202 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29202 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29205),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29207)) ->
                     let uu____29224 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29224 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29227,FStar_Syntax_Syntax.Comp uu____29228) ->
                     let uu____29237 =
                       let uu___3825_29240 = problem  in
                       let uu____29243 =
                         let uu____29244 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29244
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3825_29240.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29243;
                         FStar_TypeChecker_Common.relation =
                           (uu___3825_29240.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3825_29240.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3825_29240.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3825_29240.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3825_29240.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3825_29240.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3825_29240.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3825_29240.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29237 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29245,FStar_Syntax_Syntax.Comp uu____29246) ->
                     let uu____29255 =
                       let uu___3825_29258 = problem  in
                       let uu____29261 =
                         let uu____29262 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29262
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3825_29258.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29261;
                         FStar_TypeChecker_Common.relation =
                           (uu___3825_29258.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3825_29258.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3825_29258.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3825_29258.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3825_29258.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3825_29258.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3825_29258.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3825_29258.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29255 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29263,FStar_Syntax_Syntax.GTotal uu____29264) ->
                     let uu____29273 =
                       let uu___3837_29276 = problem  in
                       let uu____29279 =
                         let uu____29280 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29280
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3837_29276.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3837_29276.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3837_29276.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29279;
                         FStar_TypeChecker_Common.element =
                           (uu___3837_29276.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3837_29276.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3837_29276.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3837_29276.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3837_29276.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3837_29276.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29273 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29281,FStar_Syntax_Syntax.Total uu____29282) ->
                     let uu____29291 =
                       let uu___3837_29294 = problem  in
                       let uu____29297 =
                         let uu____29298 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29298
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3837_29294.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3837_29294.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3837_29294.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29297;
                         FStar_TypeChecker_Common.element =
                           (uu___3837_29294.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3837_29294.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3837_29294.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3837_29294.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3837_29294.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3837_29294.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29291 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29299,FStar_Syntax_Syntax.Comp uu____29300) ->
                     let uu____29301 =
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
                     if uu____29301
                     then
                       let uu____29304 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29304 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29311 =
                            let uu____29316 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29316
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29325 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29326 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29325, uu____29326))
                             in
                          match uu____29311 with
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
                           (let uu____29334 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29334
                            then
                              let uu____29339 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name
                                 in
                              let uu____29341 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____29339 uu____29341
                            else ());
                           (let uu____29346 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29346 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29349 =
                                  mklstr
                                    (fun uu____29356  ->
                                       let uu____29357 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29359 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29357 uu____29359)
                                   in
                                giveup env uu____29349 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29370 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29370 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29420 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29420 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29445 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29476  ->
                match uu____29476 with
                | (u1,u2) ->
                    let uu____29484 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29486 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29484 uu____29486))
         in
      FStar_All.pipe_right uu____29445 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29523,[])) when
          let uu____29550 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29550 -> "{}"
      | uu____29553 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29580 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29580
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29592 =
              FStar_List.map
                (fun uu____29605  ->
                   match uu____29605 with
                   | (uu____29612,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29592 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29623 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29623 imps
  
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
                  let uu____29680 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29680
                  then
                    let uu____29688 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29690 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29688
                      (rel_to_string rel) uu____29690
                  else "TOP"  in
                let uu____29696 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29696 with
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
              let uu____29756 =
                let uu____29759 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun uu____29762  ->
                     FStar_Pervasives_Native.Some uu____29762) uu____29759
                 in
              FStar_Syntax_Syntax.new_bv uu____29756 t1  in
            let uu____29763 =
              let uu____29768 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29768
               in
            match uu____29763 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29826 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29826
         then
           let uu____29831 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29831
         else ());
        (let uu____29838 =
           FStar_Util.record_time (fun uu____29845  -> solve env probs)  in
         match uu____29838 with
         | (sol,ms) ->
             ((let uu____29857 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29857
               then
                 let uu____29862 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29862
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29875 =
                     FStar_Util.record_time
                       (fun uu____29882  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29875 with
                    | ((),ms1) ->
                        ((let uu____29893 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29893
                          then
                            let uu____29898 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29898
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29910 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29910
                     then
                       let uu____29917 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29917
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
          ((let uu____29943 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29943
            then
              let uu____29948 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29948
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29956 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29956
             then
               let uu____29961 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29961
             else ());
            (let f2 =
               let uu____29967 =
                 let uu____29968 = FStar_Syntax_Util.unmeta f1  in
                 uu____29968.FStar_Syntax_Syntax.n  in
               match uu____29967 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29972 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3954_29973 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3954_29973.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3954_29973.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3954_29973.FStar_TypeChecker_Common.implicits)
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
            let uu____30016 =
              let uu____30017 =
                let uu____30018 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____30019  ->
                       FStar_TypeChecker_Common.NonTrivial uu____30019)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30018;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____30017  in
            FStar_All.pipe_left
              (fun uu____30026  -> FStar_Pervasives_Native.Some uu____30026)
              uu____30016
  
let with_guard_no_simp :
  'uuuuuu30036 .
    'uuuuuu30036 ->
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
            let uu____30076 =
              let uu____30077 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____30078  ->
                     FStar_TypeChecker_Common.NonTrivial uu____30078)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30077;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30076
  
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
          (let uu____30111 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30111
           then
             let uu____30116 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30118 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30116
               uu____30118
           else ());
          (let uu____30123 =
             let uu____30128 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30128
              in
           match uu____30123 with
           | (prob,wl) ->
               let g =
                 let uu____30136 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30144  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30136  in
               ((let uu____30162 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30162
                 then
                   let uu____30167 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30167
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
        let uu____30188 = try_teq true env t1 t2  in
        match uu____30188 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30193 = FStar_TypeChecker_Env.get_range env  in
              let uu____30194 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30193 uu____30194);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30202 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30202
              then
                let uu____30207 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30209 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30211 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30207
                  uu____30209 uu____30211
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
        (let uu____30235 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30235
         then
           let uu____30240 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30242 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30240
             uu____30242
         else ());
        (let uu____30247 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30247 with
         | (prob,x,wl) ->
             let g =
               let uu____30262 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30271  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30262  in
             ((let uu____30289 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30289
               then
                 let uu____30294 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30294
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30302 =
                     let uu____30303 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30303 g1  in
                   FStar_Pervasives_Native.Some uu____30302)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30325 = FStar_TypeChecker_Env.get_range env  in
          let uu____30326 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30325 uu____30326
  
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
        (let uu____30355 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30355
         then
           let uu____30360 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30362 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30360 uu____30362
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30373 =
           let uu____30380 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30380 "sub_comp"
            in
         match uu____30373 with
         | (prob,wl) ->
             let wl1 =
               let uu___4025_30391 = wl  in
               {
                 attempting = (uu___4025_30391.attempting);
                 wl_deferred = (uu___4025_30391.wl_deferred);
                 ctr = (uu___4025_30391.ctr);
                 defer_ok = (uu___4025_30391.defer_ok);
                 smt_ok = (uu___4025_30391.smt_ok);
                 umax_heuristic_ok = (uu___4025_30391.umax_heuristic_ok);
                 tcenv = (uu___4025_30391.tcenv);
                 wl_implicits = (uu___4025_30391.wl_implicits);
                 repr_subcomp_allowed = true
               }  in
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30396 =
                 FStar_Util.record_time
                   (fun uu____30408  ->
                      let uu____30409 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____30418  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30409)
                  in
               match uu____30396 with
               | (r,ms) ->
                   ((let uu____30446 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30446
                     then
                       let uu____30451 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30453 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30455 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30451 uu____30453
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30455
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
      fun uu____30493  ->
        match uu____30493 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30536 =
                 let uu____30542 =
                   let uu____30544 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30546 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30544 uu____30546
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30542)  in
               let uu____30550 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30536 uu____30550)
               in
            let equiv v v' =
              let uu____30563 =
                let uu____30568 = FStar_Syntax_Subst.compress_univ v  in
                let uu____30569 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30568, uu____30569)  in
              match uu____30563 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30593 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v  ->
                      let uu____30624 = FStar_Syntax_Subst.compress_univ v
                         in
                      match uu____30624 with
                      | FStar_Syntax_Syntax.U_unif uu____30631 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30662  ->
                                    match uu____30662 with
                                    | (u,v') ->
                                        let uu____30671 = equiv v v'  in
                                        if uu____30671
                                        then
                                          let uu____30676 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____30676 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v)]
                      | uu____30697 -> []))
               in
            let uu____30702 =
              let wl =
                let uu___4068_30706 = empty_worklist env  in
                {
                  attempting = (uu___4068_30706.attempting);
                  wl_deferred = (uu___4068_30706.wl_deferred);
                  ctr = (uu___4068_30706.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4068_30706.smt_ok);
                  umax_heuristic_ok = (uu___4068_30706.umax_heuristic_ok);
                  tcenv = (uu___4068_30706.tcenv);
                  wl_implicits = (uu___4068_30706.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4068_30706.repr_subcomp_allowed)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30725  ->
                      match uu____30725 with
                      | (lb,v) ->
                          let uu____30732 =
                            solve_universe_eq (~- Prims.int_one) wl lb v  in
                          (match uu____30732 with
                           | USolved wl1 -> ()
                           | uu____30735 -> fail lb v)))
               in
            let rec check_ineq uu____30746 =
              match uu____30746 with
              | (u,v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v  in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30758) -> true
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
                      uu____30786,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30788,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30801) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v1)))
                   | (uu____30809,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v2  -> check_ineq (u1, v2)))
                   | uu____30818 -> false)
               in
            let uu____30824 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30841  ->
                      match uu____30841 with
                      | (u,v) ->
                          let uu____30849 = check_ineq (u, v)  in
                          if uu____30849
                          then true
                          else
                            ((let uu____30857 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30857
                              then
                                let uu____30862 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30864 =
                                  FStar_Syntax_Print.univ_to_string v  in
                                FStar_Util.print2 "%s </= %s" uu____30862
                                  uu____30864
                              else ());
                             false)))
               in
            if uu____30824
            then ()
            else
              ((let uu____30874 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30874
                then
                  ((let uu____30880 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30880);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30892 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30892))
                else ());
               (let uu____30905 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30905))
  
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
          let fail uu____30985 =
            match uu____30985 with
            | (d,s) ->
                let msg = explain env d s  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d)
             in
          let wl =
            let uu___4146_31008 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
            {
              attempting = (uu___4146_31008.attempting);
              wl_deferred = (uu___4146_31008.wl_deferred);
              ctr = (uu___4146_31008.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4146_31008.umax_heuristic_ok);
              tcenv = (uu___4146_31008.tcenv);
              wl_implicits = (uu___4146_31008.wl_implicits);
              repr_subcomp_allowed = (uu___4146_31008.repr_subcomp_allowed)
            }  in
          (let uu____31011 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____31011
           then
             let uu____31016 = FStar_Util.string_of_bool defer_ok  in
             let uu____31018 = wl_to_string wl  in
             let uu____31020 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits)
                in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____31016 uu____31018 uu____31020
           else ());
          (let g1 =
             let uu____31026 = solve_and_commit env wl fail  in
             match uu____31026 with
             | FStar_Pervasives_Native.Some
                 (uu____31033::uu____31034,uu____31035) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred,imps) ->
                 let uu___4161_31064 = g  in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4161_31064.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4161_31064.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____31065 ->
                 failwith "Impossible: should have raised a failure already"
              in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let uu___4166_31074 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4166_31074.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred =
                (uu___4166_31074.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs = ([], []);
              FStar_TypeChecker_Common.implicits =
                (uu___4166_31074.FStar_TypeChecker_Common.implicits)
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
            let uu___4181_31171 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4181_31171.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4181_31171.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4181_31171.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____31172 =
            let uu____31174 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____31174  in
          if uu____31172
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug
                  then
                    (let uu____31186 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____31187 =
                       let uu____31189 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____31189
                        in
                     FStar_Errors.diag uu____31186 uu____31187)
                  else ();
                  (let vc1 =
                     let uu____31195 =
                       let uu____31199 =
                         let uu____31201 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____31201  in
                       FStar_Pervasives_Native.Some uu____31199  in
                     FStar_Profiling.profile
                       (fun uu____31204  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____31195 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug
                   then
                     (let uu____31208 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31209 =
                        let uu____31211 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31211
                         in
                      FStar_Errors.diag uu____31208 uu____31209)
                   else ();
                   (let uu____31217 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31217
                      "discharge_guard'" env vc1);
                   (let uu____31219 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31219 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug
                           then
                             (let uu____31228 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31229 =
                                let uu____31231 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31231
                                 in
                              FStar_Errors.diag uu____31228 uu____31229)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug
                           then
                             (let uu____31241 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31242 =
                                let uu____31244 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31244
                                 in
                              FStar_Errors.diag uu____31241 uu____31242)
                           else ();
                           (let vcs =
                              let uu____31258 = FStar_Options.use_tactics ()
                                 in
                              if uu____31258
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31280  ->
                                     (let uu____31282 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        (fun uu____31284  -> ()) uu____31282);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31327  ->
                                              match uu____31327 with
                                              | (env1,goal,opts) ->
                                                  let uu____31343 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31343, opts)))))
                              else
                                (let uu____31347 =
                                   let uu____31354 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31354)  in
                                 [uu____31347])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31387  ->
                                    match uu____31387 with
                                    | (env1,goal,opts) ->
                                        let uu____31397 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31397 with
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
                                                (let uu____31408 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31409 =
                                                   let uu____31411 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31413 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31411 uu____31413
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31408 uu____31409)
                                              else ();
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
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31423
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31420 uu____31421)
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
      let uu____31441 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31441 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31450 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31450
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31464 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31464 with
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
        let uu____31494 = try_teq false env t1 t2  in
        match uu____31494 with
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
            let uu____31538 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31538 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31551 ->
                     let uu____31564 =
                       let uu____31565 = FStar_Syntax_Subst.compress r  in
                       uu____31565.FStar_Syntax_Syntax.n  in
                     (match uu____31564 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31570) ->
                          unresolved ctx_u'
                      | uu____31587 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31611 = acc  in
            match uu____31611 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd::tl ->
                     let uu____31630 = hd  in
                     (match uu____31630 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl
                          else
                            (let uu____31641 = unresolved ctx_u  in
                             if uu____31641
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd :: out), changed) tl
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31665 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31665
                                     then
                                       let uu____31669 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31669
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31678 = teq_nosmt env1 t tm
                                          in
                                       match uu____31678 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4294_31688 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4294_31688.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4294_31688.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4294_31688.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4294_31688.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4294_31688.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4294_31688.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4294_31688.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd1 =
                                       let uu___4297_31696 = hd  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4297_31696.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4297_31696.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4297_31696.FStar_TypeChecker_Common.imp_range)
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
                                    let uu___4301_31707 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4301_31707.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4301_31707.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4301_31707.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4301_31707.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4301_31707.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4301_31707.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4301_31707.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4301_31707.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4301_31707.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4301_31707.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4301_31707.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4301_31707.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4301_31707.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4301_31707.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4301_31707.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4301_31707.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4301_31707.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4301_31707.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4301_31707.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4301_31707.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4301_31707.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4301_31707.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4301_31707.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4301_31707.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4301_31707.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4301_31707.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4301_31707.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4301_31707.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4301_31707.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4301_31707.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4301_31707.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4301_31707.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4301_31707.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4301_31707.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4301_31707.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4301_31707.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4301_31707.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4301_31707.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4301_31707.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4301_31707.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4301_31707.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4301_31707.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4301_31707.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4301_31707.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4301_31707.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4306_31712 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4306_31712.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4306_31712.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4306_31712.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4306_31712.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4306_31712.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4306_31712.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4306_31712.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4306_31712.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4306_31712.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4306_31712.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4306_31712.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4306_31712.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4306_31712.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4306_31712.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4306_31712.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4306_31712.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4306_31712.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4306_31712.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4306_31712.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4306_31712.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4306_31712.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4306_31712.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4306_31712.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4306_31712.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4306_31712.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4306_31712.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4306_31712.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4306_31712.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4306_31712.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4306_31712.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4306_31712.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4306_31712.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4306_31712.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4306_31712.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4306_31712.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4306_31712.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4306_31712.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4306_31712.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4306_31712.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4306_31712.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4306_31712.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4306_31712.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4306_31712.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4306_31712.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4306_31712.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31717 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31717
                                   then
                                     let uu____31722 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31724 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31726 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31728 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31722 uu____31724 uu____31726
                                       reason uu____31728
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4312_31735  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31742 =
                                             let uu____31752 =
                                               let uu____31760 =
                                                 let uu____31762 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31764 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31766 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31762 uu____31764
                                                   uu____31766
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31760, r)
                                                in
                                             [uu____31752]  in
                                           FStar_Errors.add_errors
                                             uu____31742);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31785 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31796  ->
                                               let uu____31797 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31799 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31801 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31797 uu____31799
                                                 reason uu____31801)) env2 g1
                                         true
                                        in
                                     match uu____31785 with
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
          let uu___4324_31809 = g  in
          let uu____31810 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4324_31809.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4324_31809.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4324_31809.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31810
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
        let uu____31850 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31850 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31851 = discharge_guard env g1  in
          FStar_All.pipe_left (fun uu____31852  -> ()) uu____31851
      | imp::uu____31854 ->
          let uu____31857 =
            let uu____31863 =
              let uu____31865 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31867 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31865 uu____31867
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31863)
             in
          FStar_Errors.raise_error uu____31857
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31887 = teq env t1 t2  in
        force_trivial_guard env uu____31887
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31906 = teq_nosmt env t1 t2  in
        match uu____31906 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4349_31925 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4349_31925.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4349_31925.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4349_31925.FStar_TypeChecker_Common.implicits)
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
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31966
             uu____31968
         else ());
        (let uu____31973 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31973 with
         | (prob,x,wl) ->
             let g =
               let uu____31992 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____32001  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31992  in
             ((let uu____32019 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____32019
               then
                 let uu____32024 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____32026 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____32028 =
                   let uu____32030 = FStar_Util.must g  in
                   guard_to_string env uu____32030  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____32024 uu____32026 uu____32028
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
        let uu____32067 = check_subtyping env t1 t2  in
        match uu____32067 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32086 =
              let uu____32087 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____32087 g  in
            FStar_Pervasives_Native.Some uu____32086
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32106 = check_subtyping env t1 t2  in
        match uu____32106 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32125 =
              let uu____32126 =
                let uu____32127 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____32127]  in
              FStar_TypeChecker_Env.close_guard env uu____32126 g  in
            FStar_Pervasives_Native.Some uu____32125
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32165 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32165
         then
           let uu____32170 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32172 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32170
             uu____32172
         else ());
        (let uu____32177 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32177 with
         | (prob,x,wl) ->
             let g =
               let uu____32192 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32201  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32192  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32222 =
                      let uu____32223 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32223]  in
                    FStar_TypeChecker_Env.close_guard env uu____32222 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32264 = subtype_nosmt env t1 t2  in
        match uu____32264 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  