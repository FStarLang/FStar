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
                FStar_Syntax_Syntax.ctx_uvar_meta_t
                  FStar_Pervasives_Native.option ->
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
                    let uu____529 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____529;
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
                   (let uu____561 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace")
                       in
                    if uu____561
                    then
                      let uu____565 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                         in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____565
                    else ());
                   (ctx_uvar, t,
                     ((let uu___73_571 = wl  in
                       {
                         attempting = (uu___73_571.attempting);
                         wl_deferred = (uu___73_571.wl_deferred);
                         ctr = (uu___73_571.ctr);
                         defer_ok = (uu___73_571.defer_ok);
                         smt_ok = (uu___73_571.smt_ok);
                         umax_heuristic_ok = (uu___73_571.umax_heuristic_ok);
                         tcenv = (uu___73_571.tcenv);
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
            let uu___79_604 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___79_604.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___79_604.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___79_604.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___79_604.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___79_604.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___79_604.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___79_604.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___79_604.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___79_604.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___79_604.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___79_604.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___79_604.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___79_604.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___79_604.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___79_604.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___79_604.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___79_604.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___79_604.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___79_604.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___79_604.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___79_604.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___79_604.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___79_604.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___79_604.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___79_604.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___79_604.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___79_604.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___79_604.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___79_604.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___79_604.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___79_604.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___79_604.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___79_604.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___79_604.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___79_604.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___79_604.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___79_604.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___79_604.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___79_604.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___79_604.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___79_604.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___79_604.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___79_604.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___79_604.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___79_604.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___79_604.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____606 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____606 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____693 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____728 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____758 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____769 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____780 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_798  ->
    match uu___0_798 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____810 = FStar_Syntax_Util.head_and_args t  in
    match uu____810 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____873 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____875 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____890 =
                     let uu____892 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____892  in
                   FStar_Util.format1 "@<%s>" uu____890
                in
             let uu____896 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____873 uu____875 uu____896
         | uu____899 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_911  ->
      match uu___1_911 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____916 =
            let uu____920 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____922 =
              let uu____926 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____928 =
                let uu____932 =
                  let uu____936 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____936]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____932
                 in
              uu____926 :: uu____928  in
            uu____920 :: uu____922  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____916
      | FStar_TypeChecker_Common.CProb p ->
          let uu____947 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____949 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____951 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____947 uu____949
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____951
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_965  ->
      match uu___2_965 with
      | UNIV (u,t) ->
          let x =
            let uu____971 = FStar_Options.hide_uvar_nums ()  in
            if uu____971
            then "?"
            else
              (let uu____978 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____978 FStar_Util.string_of_int)
             in
          let uu____982 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____982
      | TERM (u,t) ->
          let x =
            let uu____989 = FStar_Options.hide_uvar_nums ()  in
            if uu____989
            then "?"
            else
              (let uu____996 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____996 FStar_Util.string_of_int)
             in
          let uu____1000 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1000
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1019 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1019 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1040 =
      let uu____1044 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1044
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1040 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1063 .
    (FStar_Syntax_Syntax.term * 'Auu____1063) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1082 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1103  ->
              match uu____1103 with
              | (x,uu____1110) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1082 (FStar_String.concat " ")
  
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
        (let uu____1150 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1150
         then
           let uu____1155 = FStar_Thunk.force reason  in
           let uu____1158 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1155 uu____1158
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1181 = FStar_Thunk.mk (fun uu____1184  -> reason)  in
        giveup env uu____1181 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1190  ->
    match uu___3_1190 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1196 .
    'Auu____1196 FStar_TypeChecker_Common.problem ->
      'Auu____1196 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___143_1208 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___143_1208.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___143_1208.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___143_1208.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___143_1208.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___143_1208.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___143_1208.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___143_1208.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1216 .
    'Auu____1216 FStar_TypeChecker_Common.problem ->
      'Auu____1216 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1236  ->
    match uu___4_1236 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1242  -> FStar_TypeChecker_Common.TProb _1242)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1248  -> FStar_TypeChecker_Common.CProb _1248)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1254  ->
    match uu___5_1254 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___155_1260 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___155_1260.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___155_1260.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___155_1260.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___155_1260.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___155_1260.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___155_1260.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___155_1260.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___155_1260.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___155_1260.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___159_1268 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___159_1268.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___159_1268.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___159_1268.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___159_1268.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___159_1268.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___159_1268.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___159_1268.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___159_1268.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___159_1268.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1281  ->
      match uu___6_1281 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1288  ->
    match uu___7_1288 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1301  ->
    match uu___8_1301 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1316  ->
    match uu___9_1316 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1331  ->
    match uu___10_1331 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1345  ->
    match uu___11_1345 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1359  ->
    match uu___12_1359 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1371  ->
    match uu___13_1371 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1387 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1387) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1417 =
          let uu____1419 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1419  in
        if uu____1417
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1456)::bs ->
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
          let uu____1503 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1527 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1527]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1503
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1555 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1579 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1579]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1555
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1626 =
          let uu____1628 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1628  in
        if uu____1626
        then ()
        else
          (let uu____1633 =
             let uu____1636 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1636
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1633 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1685 =
          let uu____1687 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1687  in
        if uu____1685
        then ()
        else
          (let uu____1692 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1692)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1712 =
        let uu____1714 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1714  in
      if uu____1712
      then ()
      else
        (let msgf m =
           let uu____1728 =
             let uu____1730 =
               let uu____1732 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____1732 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____1730  in
           Prims.op_Hat msg uu____1728  in
         (let uu____1737 = msgf "scope"  in
          let uu____1740 = p_scope prob  in
          def_scope_wf uu____1737 (p_loc prob) uu____1740);
         (let uu____1752 = msgf "guard"  in
          def_check_scoped uu____1752 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1759 = msgf "lhs"  in
                def_check_scoped uu____1759 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1762 = msgf "rhs"  in
                def_check_scoped uu____1762 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1769 = msgf "lhs"  in
                def_check_scoped_comp uu____1769 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1772 = msgf "rhs"  in
                def_check_scoped_comp uu____1772 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___252_1793 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___252_1793.wl_deferred);
          ctr = (uu___252_1793.ctr);
          defer_ok = (uu___252_1793.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___252_1793.umax_heuristic_ok);
          tcenv = (uu___252_1793.tcenv);
          wl_implicits = (uu___252_1793.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1801 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1801 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___256_1824 = empty_worklist env  in
      let uu____1825 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1825;
        wl_deferred = (uu___256_1824.wl_deferred);
        ctr = (uu___256_1824.ctr);
        defer_ok = (uu___256_1824.defer_ok);
        smt_ok = (uu___256_1824.smt_ok);
        umax_heuristic_ok = (uu___256_1824.umax_heuristic_ok);
        tcenv = (uu___256_1824.tcenv);
        wl_implicits = (uu___256_1824.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___261_1846 = wl  in
        {
          attempting = (uu___261_1846.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___261_1846.ctr);
          defer_ok = (uu___261_1846.defer_ok);
          smt_ok = (uu___261_1846.smt_ok);
          umax_heuristic_ok = (uu___261_1846.umax_heuristic_ok);
          tcenv = (uu___261_1846.tcenv);
          wl_implicits = (uu___261_1846.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____1873 = FStar_Thunk.mkv reason  in defer uu____1873 prob wl
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___269_1892 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___269_1892.wl_deferred);
         ctr = (uu___269_1892.ctr);
         defer_ok = (uu___269_1892.defer_ok);
         smt_ok = (uu___269_1892.smt_ok);
         umax_heuristic_ok = (uu___269_1892.umax_heuristic_ok);
         tcenv = (uu___269_1892.tcenv);
         wl_implicits = (uu___269_1892.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1906 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1906 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____1940 = FStar_Syntax_Util.type_u ()  in
            match uu____1940 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____1952 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____1952 with
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
                        let uu____2236 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2236;
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
                  (let uu____2310 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2310 with
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
                  (let uu____2398 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2398 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2436 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2436 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2436 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2436 FStar_TypeChecker_Common.problem *
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
                          let uu____2504 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2504]  in
                        let uu____2523 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2523
                     in
                  let uu____2526 =
                    let uu____2533 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___352_2544 = wl  in
                       {
                         attempting = (uu___352_2544.attempting);
                         wl_deferred = (uu___352_2544.wl_deferred);
                         ctr = (uu___352_2544.ctr);
                         defer_ok = (uu___352_2544.defer_ok);
                         smt_ok = (uu___352_2544.smt_ok);
                         umax_heuristic_ok =
                           (uu___352_2544.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___352_2544.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2533
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2526 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2556 =
                              let uu____2561 =
                                let uu____2562 =
                                  let uu____2571 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2571
                                   in
                                [uu____2562]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2561  in
                            uu____2556 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2599 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2599;
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
                let uu____2647 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2647;
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
  'Auu____2662 .
    worklist ->
      'Auu____2662 FStar_TypeChecker_Common.problem ->
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
              let uu____2695 =
                let uu____2698 =
                  let uu____2699 =
                    let uu____2706 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2706)  in
                  FStar_Syntax_Syntax.NT uu____2699  in
                [uu____2698]  in
              FStar_Syntax_Subst.subst uu____2695 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2728 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2728
        then
          let uu____2736 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2739 = prob_to_string env d  in
          let uu____2741 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____2748 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2736 uu____2739 uu____2741 uu____2748
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2760 -> failwith "impossible"  in
           let uu____2763 =
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
           match uu____2763 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2806  ->
            match uu___15_2806 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2818 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2822 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2822 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2853  ->
           match uu___16_2853 with
           | UNIV uu____2856 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2863 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2863
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
        (fun uu___17_2891  ->
           match uu___17_2891 with
           | UNIV (u',t) ->
               let uu____2896 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2896
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2903 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2915 =
        let uu____2916 =
          let uu____2917 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2917
           in
        FStar_Syntax_Subst.compress uu____2916  in
      FStar_All.pipe_right uu____2915 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2929 =
        let uu____2930 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____2930  in
      FStar_All.pipe_right uu____2929 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2942 =
        let uu____2946 =
          let uu____2948 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____2948  in
        FStar_Pervasives_Native.Some uu____2946  in
      FStar_Profiling.profile (fun uu____2951  -> sn' env t) uu____2942
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
          let uu____2976 =
            let uu____2980 =
              let uu____2982 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____2982  in
            FStar_Pervasives_Native.Some uu____2980  in
          FStar_Profiling.profile
            (fun uu____2985  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____2976
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2993 = FStar_Syntax_Util.head_and_args t  in
    match uu____2993 with
    | (h,uu____3012) ->
        let uu____3037 =
          let uu____3038 = FStar_Syntax_Subst.compress h  in
          uu____3038.FStar_Syntax_Syntax.n  in
        (match uu____3037 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3043 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3056 =
        let uu____3060 =
          let uu____3062 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3062  in
        FStar_Pervasives_Native.Some uu____3060  in
      FStar_Profiling.profile
        (fun uu____3067  ->
           let uu____3068 = should_strongly_reduce t  in
           if uu____3068
           then
             let uu____3071 =
               let uu____3072 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3072  in
             FStar_All.pipe_right uu____3071 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3056 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'Auu____3083 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3083) ->
        (FStar_Syntax_Syntax.term * 'Auu____3083)
  =
  fun env  ->
    fun t  ->
      let uu____3106 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3106, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3158  ->
              match uu____3158 with
              | (x,imp) ->
                  let uu____3177 =
                    let uu___458_3178 = x  in
                    let uu____3179 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___458_3178.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___458_3178.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3179
                    }  in
                  (uu____3177, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3203 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3203
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3207 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3207
        | uu____3210 -> u2  in
      let uu____3211 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3211
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3228 =
          let uu____3232 =
            let uu____3234 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3234  in
          FStar_Pervasives_Native.Some uu____3232  in
        FStar_Profiling.profile
          (fun uu____3237  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3228 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
                (let uu____3359 = norm_refinement env t12  in
                 match uu____3359 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3374;
                     FStar_Syntax_Syntax.vars = uu____3375;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3399 =
                       let uu____3401 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3403 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3401 uu____3403
                        in
                     failwith uu____3399)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3419 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3419
          | FStar_Syntax_Syntax.Tm_uinst uu____3420 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3457 =
                   let uu____3458 = FStar_Syntax_Subst.compress t1'  in
                   uu____3458.FStar_Syntax_Syntax.n  in
                 match uu____3457 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3473 -> aux true t1'
                 | uu____3481 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3496 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3527 =
                   let uu____3528 = FStar_Syntax_Subst.compress t1'  in
                   uu____3528.FStar_Syntax_Syntax.n  in
                 match uu____3527 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3543 -> aux true t1'
                 | uu____3551 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3566 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3613 =
                   let uu____3614 = FStar_Syntax_Subst.compress t1'  in
                   uu____3614.FStar_Syntax_Syntax.n  in
                 match uu____3613 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3629 -> aux true t1'
                 | uu____3637 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3652 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3667 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3682 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3697 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3712 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3741 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3774 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3795 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3822 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3850 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3887 ->
              let uu____3894 =
                let uu____3896 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3898 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3896 uu____3898
                 in
              failwith uu____3894
          | FStar_Syntax_Syntax.Tm_ascribed uu____3913 ->
              let uu____3940 =
                let uu____3942 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3944 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3942 uu____3944
                 in
              failwith uu____3940
          | FStar_Syntax_Syntax.Tm_delayed uu____3959 ->
              let uu____3974 =
                let uu____3976 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3978 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3976 uu____3978
                 in
              failwith uu____3974
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3993 =
                let uu____3995 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3997 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3995 uu____3997
                 in
              failwith uu____3993
           in
        let uu____4012 = whnf env t1  in aux false uu____4012
  
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
      let uu____4057 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4057 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4098 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4098, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4125 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4125 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4185  ->
    match uu____4185 with
    | (t_base,refopt) ->
        let uu____4216 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4216 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4258 =
      let uu____4262 =
        let uu____4265 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4290  ->
                  match uu____4290 with | (uu____4298,uu____4299,x) -> x))
           in
        FStar_List.append wl.attempting uu____4265  in
      FStar_List.map (wl_prob_to_string wl) uu____4262  in
    FStar_All.pipe_right uu____4258 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____4320 .
    ('Auu____4320 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4332  ->
    match uu____4332 with
    | (uu____4339,c,args) ->
        let uu____4342 = print_ctx_uvar c  in
        let uu____4344 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4342 uu____4344
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4354 = FStar_Syntax_Util.head_and_args t  in
    match uu____4354 with
    | (head1,_args) ->
        let uu____4398 =
          let uu____4399 = FStar_Syntax_Subst.compress head1  in
          uu____4399.FStar_Syntax_Syntax.n  in
        (match uu____4398 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4403 -> true
         | uu____4417 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4425 = FStar_Syntax_Util.head_and_args t  in
    match uu____4425 with
    | (head1,_args) ->
        let uu____4468 =
          let uu____4469 = FStar_Syntax_Subst.compress head1  in
          uu____4469.FStar_Syntax_Syntax.n  in
        (match uu____4468 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4473) -> u
         | uu____4490 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4515 = FStar_Syntax_Util.head_and_args t  in
      match uu____4515 with
      | (head1,args) ->
          let uu____4562 =
            let uu____4563 = FStar_Syntax_Subst.compress head1  in
            uu____4563.FStar_Syntax_Syntax.n  in
          (match uu____4562 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4571)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4604 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_4629  ->
                         match uu___18_4629 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4634 =
                               let uu____4635 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4635.FStar_Syntax_Syntax.n  in
                             (match uu____4634 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4640 -> false)
                         | uu____4642 -> true))
                  in
               (match uu____4604 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4667 =
                        FStar_List.collect
                          (fun uu___19_4679  ->
                             match uu___19_4679 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4683 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4683]
                             | uu____4684 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4667 FStar_List.rev  in
                    let uu____4707 =
                      let uu____4714 =
                        let uu____4723 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_4745  ->
                                  match uu___20_4745 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4749 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4749]
                                  | uu____4750 -> []))
                           in
                        FStar_All.pipe_right uu____4723 FStar_List.rev  in
                      let uu____4773 =
                        let uu____4776 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4776  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4714 uu____4773
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____4707 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4812  ->
                                match uu____4812 with
                                | (x,i) ->
                                    let uu____4831 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4831, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4862  ->
                                match uu____4862 with
                                | (a,i) ->
                                    let uu____4881 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4881, i)) args_sol
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
           | uu____4903 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4925 =
          let uu____4948 =
            let uu____4949 = FStar_Syntax_Subst.compress k  in
            uu____4949.FStar_Syntax_Syntax.n  in
          match uu____4948 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5031 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5031)
              else
                (let uu____5066 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5066 with
                 | (ys',t1,uu____5099) ->
                     let uu____5104 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5104))
          | uu____5143 ->
              let uu____5144 =
                let uu____5149 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5149)  in
              ((ys, t), uu____5144)
           in
        match uu____4925 with
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
                 let uu____5244 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5244 c  in
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
               (let uu____5322 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5322
                then
                  let uu____5327 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5329 = print_ctx_uvar uv  in
                  let uu____5331 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5327 uu____5329 uu____5331
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5340 =
                   let uu____5342 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5342  in
                 let uu____5345 =
                   let uu____5348 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5348
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5340 uu____5345 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5381 =
               let uu____5382 =
                 let uu____5384 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5386 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5384 uu____5386
                  in
               failwith uu____5382  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5452  ->
                       match uu____5452 with
                       | (a,i) ->
                           let uu____5473 =
                             let uu____5474 = FStar_Syntax_Subst.compress a
                                in
                             uu____5474.FStar_Syntax_Syntax.n  in
                           (match uu____5473 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5500 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5510 =
                 let uu____5512 = is_flex g  in Prims.op_Negation uu____5512
                  in
               if uu____5510
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5521 = destruct_flex_t g wl  in
                  match uu____5521 with
                  | ((uu____5526,uv1,args),wl1) ->
                      ((let uu____5531 = args_as_binders args  in
                        assign_solution uu____5531 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___711_5533 = wl1  in
              {
                attempting = (uu___711_5533.attempting);
                wl_deferred = (uu___711_5533.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___711_5533.defer_ok);
                smt_ok = (uu___711_5533.smt_ok);
                umax_heuristic_ok = (uu___711_5533.umax_heuristic_ok);
                tcenv = (uu___711_5533.tcenv);
                wl_implicits = (uu___711_5533.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5558 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5558
         then
           let uu____5563 = FStar_Util.string_of_int pid  in
           let uu____5565 =
             let uu____5567 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5567 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5563 uu____5565
         else ());
        commit sol;
        (let uu___719_5581 = wl  in
         {
           attempting = (uu___719_5581.attempting);
           wl_deferred = (uu___719_5581.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___719_5581.defer_ok);
           smt_ok = (uu___719_5581.smt_ok);
           umax_heuristic_ok = (uu___719_5581.umax_heuristic_ok);
           tcenv = (uu___719_5581.tcenv);
           wl_implicits = (uu___719_5581.wl_implicits)
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
          (let uu____5617 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____5617
           then
             let uu____5622 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____5626 =
               let uu____5628 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____5628 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5622 uu____5626
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
        let uu____5663 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5663 FStar_Util.set_elements  in
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
      let uu____5703 = occurs uk t  in
      match uu____5703 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5742 =
                 let uu____5744 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5746 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5744 uu____5746
                  in
               FStar_Pervasives_Native.Some uu____5742)
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
            let uu____5866 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5866 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5917 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5974  ->
             match uu____5974 with
             | (x,uu____5986) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6004 = FStar_List.last bs  in
      match uu____6004 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6028) ->
          let uu____6039 =
            FStar_Util.prefix_until
              (fun uu___21_6054  ->
                 match uu___21_6054 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6057 -> false) g
             in
          (match uu____6039 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6071,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6108 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6108 with
        | (pfx,uu____6118) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6130 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6130 with
             | (uu____6138,src',wl1) ->
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
                 | uu____6252 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6253 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6317  ->
                  fun uu____6318  ->
                    match (uu____6317, uu____6318) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6421 =
                          let uu____6423 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6423
                           in
                        if uu____6421
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6457 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6457
                           then
                             let uu____6474 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6474)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6253 with | (isect,uu____6524) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6560 'Auu____6561 .
    (FStar_Syntax_Syntax.bv * 'Auu____6560) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6561) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6619  ->
              fun uu____6620  ->
                match (uu____6619, uu____6620) with
                | ((a,uu____6639),(b,uu____6641)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6657 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6657) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6688  ->
           match uu____6688 with
           | (y,uu____6695) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6705 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6705) Prims.list ->
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
                   let uu____6867 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6867
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6900 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6952 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6996 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7017 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7025  ->
    match uu___22_7025 with
    | MisMatch (d1,d2) ->
        let uu____7037 =
          let uu____7039 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7041 =
            let uu____7043 =
              let uu____7045 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7045 ")"  in
            Prims.op_Hat ") (" uu____7043  in
          Prims.op_Hat uu____7039 uu____7041  in
        Prims.op_Hat "MisMatch (" uu____7037
    | HeadMatch u ->
        let uu____7052 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7052
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7061  ->
    match uu___23_7061 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7078 -> HeadMatch false
  
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
          let uu____7100 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7100 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7111 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7135 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7145 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7164 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7164
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7165 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7166 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7167 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7180 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7194 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7218) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7224,uu____7225) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7267) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7292;
             FStar_Syntax_Syntax.index = uu____7293;
             FStar_Syntax_Syntax.sort = t2;_},uu____7295)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7303 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7304 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7305 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7320 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7327 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7347 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7347
  
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
           { FStar_Syntax_Syntax.blob = uu____7366;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7367;
             FStar_Syntax_Syntax.ltyp = uu____7368;
             FStar_Syntax_Syntax.rng = uu____7369;_},uu____7370)
            ->
            let uu____7381 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7381 t21
        | (uu____7382,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7383;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7384;
             FStar_Syntax_Syntax.ltyp = uu____7385;
             FStar_Syntax_Syntax.rng = uu____7386;_})
            ->
            let uu____7397 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7397
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7409 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7409
            then FullMatch
            else
              (let uu____7414 =
                 let uu____7423 =
                   let uu____7426 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7426  in
                 let uu____7427 =
                   let uu____7430 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7430  in
                 (uu____7423, uu____7427)  in
               MisMatch uu____7414)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7436),FStar_Syntax_Syntax.Tm_uinst (g,uu____7438)) ->
            let uu____7447 = head_matches env f g  in
            FStar_All.pipe_right uu____7447 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7448) -> HeadMatch true
        | (uu____7450,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7454 = FStar_Const.eq_const c d  in
            if uu____7454
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7464),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7466)) ->
            let uu____7499 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7499
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7509),FStar_Syntax_Syntax.Tm_refine (y,uu____7511)) ->
            let uu____7520 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7520 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7522),uu____7523) ->
            let uu____7528 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7528 head_match
        | (uu____7529,FStar_Syntax_Syntax.Tm_refine (x,uu____7531)) ->
            let uu____7536 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7536 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7537,FStar_Syntax_Syntax.Tm_type
           uu____7538) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7540,FStar_Syntax_Syntax.Tm_arrow uu____7541) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7572),FStar_Syntax_Syntax.Tm_app (head',uu____7574))
            ->
            let uu____7623 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7623 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7625),uu____7626) ->
            let uu____7651 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7651 head_match
        | (uu____7652,FStar_Syntax_Syntax.Tm_app (head1,uu____7654)) ->
            let uu____7679 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7679 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7680,FStar_Syntax_Syntax.Tm_let
           uu____7681) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7709,FStar_Syntax_Syntax.Tm_match uu____7710) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7756,FStar_Syntax_Syntax.Tm_abs
           uu____7757) -> HeadMatch true
        | uu____7795 ->
            let uu____7800 =
              let uu____7809 = delta_depth_of_term env t11  in
              let uu____7812 = delta_depth_of_term env t21  in
              (uu____7809, uu____7812)  in
            MisMatch uu____7800
  
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
              let uu____7881 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7881  in
            (let uu____7883 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7883
             then
               let uu____7888 = FStar_Syntax_Print.term_to_string t  in
               let uu____7890 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7888 uu____7890
             else ());
            (let uu____7895 =
               let uu____7896 = FStar_Syntax_Util.un_uinst head1  in
               uu____7896.FStar_Syntax_Syntax.n  in
             match uu____7895 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7902 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7902 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7916 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7916
                        then
                          let uu____7921 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7921
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7926 ->
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
                      let uu____7944 =
                        let uu____7946 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7946 = FStar_Syntax_Util.Equal  in
                      if uu____7944
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7953 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7953
                          then
                            let uu____7958 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____7960 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7958
                              uu____7960
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7965 -> FStar_Pervasives_Native.None)
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
            (let uu____8117 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8117
             then
               let uu____8122 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8124 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8126 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8122
                 uu____8124 uu____8126
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8154 =
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
               match uu____8154 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8202 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8202 with
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
                  uu____8240),uu____8241)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8262 =
                      let uu____8271 = maybe_inline t11  in
                      let uu____8274 = maybe_inline t21  in
                      (uu____8271, uu____8274)  in
                    match uu____8262 with
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
                 (uu____8317,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8318))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8339 =
                      let uu____8348 = maybe_inline t11  in
                      let uu____8351 = maybe_inline t21  in
                      (uu____8348, uu____8351)  in
                    match uu____8339 with
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
             | MisMatch uu____8406 -> fail1 n_delta r t11 t21
             | uu____8415 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8430 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8430
           then
             let uu____8435 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8437 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8439 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8447 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8464 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8464
                    (fun uu____8499  ->
                       match uu____8499 with
                       | (t11,t21) ->
                           let uu____8507 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8509 =
                             let uu____8511 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8511  in
                           Prims.op_Hat uu____8507 uu____8509))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8435 uu____8437 uu____8439 uu____8447
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8528 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8528 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8543  ->
    match uu___24_8543 with
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
      let uu___1208_8592 = p  in
      let uu____8595 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8596 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1208_8592.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8595;
        FStar_TypeChecker_Common.relation =
          (uu___1208_8592.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8596;
        FStar_TypeChecker_Common.element =
          (uu___1208_8592.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1208_8592.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1208_8592.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1208_8592.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1208_8592.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1208_8592.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8611 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8611
            (fun _8616  -> FStar_TypeChecker_Common.TProb _8616)
      | FStar_TypeChecker_Common.CProb uu____8617 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8640 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8640 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8648 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8648 with
           | (lh,lhs_args) ->
               let uu____8695 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8695 with
                | (rh,rhs_args) ->
                    let uu____8742 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8755,FStar_Syntax_Syntax.Tm_uvar uu____8756)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8845 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8872,uu____8873)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8888,FStar_Syntax_Syntax.Tm_uvar uu____8889)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8904,FStar_Syntax_Syntax.Tm_arrow uu____8905)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1259_8935 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1259_8935.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1259_8935.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1259_8935.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1259_8935.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1259_8935.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1259_8935.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1259_8935.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1259_8935.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1259_8935.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8938,FStar_Syntax_Syntax.Tm_type uu____8939)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1259_8955 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1259_8955.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1259_8955.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1259_8955.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1259_8955.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1259_8955.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1259_8955.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1259_8955.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1259_8955.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1259_8955.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8958,FStar_Syntax_Syntax.Tm_uvar uu____8959)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1259_8975 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1259_8975.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1259_8975.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1259_8975.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1259_8975.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1259_8975.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1259_8975.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1259_8975.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1259_8975.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1259_8975.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8978,FStar_Syntax_Syntax.Tm_uvar uu____8979)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8994,uu____8995)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9010,FStar_Syntax_Syntax.Tm_uvar uu____9011)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9026,uu____9027) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8742 with
                     | (rank,tp1) ->
                         let uu____9040 =
                           FStar_All.pipe_right
                             (let uu___1279_9044 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1279_9044.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1279_9044.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1279_9044.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1279_9044.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1279_9044.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1279_9044.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1279_9044.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1279_9044.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1279_9044.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9047  ->
                                FStar_TypeChecker_Common.TProb _9047)
                            in
                         (rank, uu____9040))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9051 =
            FStar_All.pipe_right
              (let uu___1283_9055 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1283_9055.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1283_9055.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1283_9055.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1283_9055.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1283_9055.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1283_9055.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1283_9055.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1283_9055.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1283_9055.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9058  -> FStar_TypeChecker_Common.CProb _9058)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9051)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9118 probs =
      match uu____9118 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9199 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9220 = rank wl.tcenv hd1  in
               (match uu____9220 with
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
                      (let uu____9281 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9286 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9286)
                          in
                       if uu____9281
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
          let uu____9359 = FStar_Syntax_Util.head_and_args t  in
          match uu____9359 with
          | (hd1,uu____9378) ->
              let uu____9403 =
                let uu____9404 = FStar_Syntax_Subst.compress hd1  in
                uu____9404.FStar_Syntax_Syntax.n  in
              (match uu____9403 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9409) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9444  ->
                           match uu____9444 with
                           | (y,uu____9453) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9476  ->
                                       match uu____9476 with
                                       | (x,uu____9485) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9490 -> false)
           in
        let uu____9492 = rank tcenv p  in
        match uu____9492 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9501 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9582 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9601 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9620 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9637 = FStar_Thunk.mkv s  in UFailed uu____9637 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9652 = FStar_Thunk.mk s  in UFailed uu____9652 
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
                        let uu____9704 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9704 with
                        | (k,uu____9712) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9725 -> false)))
            | uu____9727 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9779 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9787 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9787 = Prims.int_zero))
                           in
                        if uu____9779 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9808 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9816 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9816 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9808)
               in
            let uu____9820 = filter1 u12  in
            let uu____9823 = filter1 u22  in (uu____9820, uu____9823)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9858 = filter_out_common_univs us1 us2  in
                   (match uu____9858 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9918 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9918 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9921 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9938  ->
                               let uu____9939 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____9941 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9939 uu____9941))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9967 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9967 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9993 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9993 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____9996 ->
                   ufailed_thunk
                     (fun uu____10007  ->
                        let uu____10008 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10010 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10008 uu____10010 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10013,uu____10014) ->
              let uu____10016 =
                let uu____10018 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10020 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10018 uu____10020
                 in
              failwith uu____10016
          | (FStar_Syntax_Syntax.U_unknown ,uu____10023) ->
              let uu____10024 =
                let uu____10026 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10028 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10026 uu____10028
                 in
              failwith uu____10024
          | (uu____10031,FStar_Syntax_Syntax.U_bvar uu____10032) ->
              let uu____10034 =
                let uu____10036 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10038 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10036 uu____10038
                 in
              failwith uu____10034
          | (uu____10041,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10042 =
                let uu____10044 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10046 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10044 uu____10046
                 in
              failwith uu____10042
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10076 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10076
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10093 = occurs_univ v1 u3  in
              if uu____10093
              then
                let uu____10096 =
                  let uu____10098 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10100 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10098 uu____10100
                   in
                try_umax_components u11 u21 uu____10096
              else
                (let uu____10105 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10105)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10117 = occurs_univ v1 u3  in
              if uu____10117
              then
                let uu____10120 =
                  let uu____10122 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10124 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10122 uu____10124
                   in
                try_umax_components u11 u21 uu____10120
              else
                (let uu____10129 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10129)
          | (FStar_Syntax_Syntax.U_max uu____10130,uu____10131) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10139 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10139
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10145,FStar_Syntax_Syntax.U_max uu____10146) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10154 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10154
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10160,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10162,FStar_Syntax_Syntax.U_name uu____10163) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10165) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10167) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10169,FStar_Syntax_Syntax.U_succ uu____10170) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10172,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10279 = bc1  in
      match uu____10279 with
      | (bs1,mk_cod1) ->
          let uu____10323 = bc2  in
          (match uu____10323 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10434 = aux xs ys  in
                     (match uu____10434 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10517 =
                       let uu____10524 = mk_cod1 xs  in ([], uu____10524)  in
                     let uu____10527 =
                       let uu____10534 = mk_cod2 ys  in ([], uu____10534)  in
                     (uu____10517, uu____10527)
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
                  let uu____10603 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10603 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10606 =
                    let uu____10607 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10607 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10606
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10612 = has_type_guard t1 t2  in (uu____10612, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10613 = has_type_guard t2 t1  in (uu____10613, wl)
  
let is_flex_pat :
  'Auu____10623 'Auu____10624 'Auu____10625 .
    ('Auu____10623 * 'Auu____10624 * 'Auu____10625 Prims.list) -> Prims.bool
  =
  fun uu___25_10639  ->
    match uu___25_10639 with
    | (uu____10648,uu____10649,[]) -> true
    | uu____10653 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10686 = f  in
      match uu____10686 with
      | (uu____10693,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10694;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10695;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10698;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10699;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10700;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10701;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10765  ->
                 match uu____10765 with
                 | (y,uu____10774) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10928 =
                  let uu____10943 =
                    let uu____10946 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10946  in
                  ((FStar_List.rev pat_binders), uu____10943)  in
                FStar_Pervasives_Native.Some uu____10928
            | (uu____10979,[]) ->
                let uu____11010 =
                  let uu____11025 =
                    let uu____11028 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11028  in
                  ((FStar_List.rev pat_binders), uu____11025)  in
                FStar_Pervasives_Native.Some uu____11010
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11119 =
                  let uu____11120 = FStar_Syntax_Subst.compress a  in
                  uu____11120.FStar_Syntax_Syntax.n  in
                (match uu____11119 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11140 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11140
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1611_11170 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1611_11170.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1611_11170.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11174 =
                            let uu____11175 =
                              let uu____11182 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11182)  in
                            FStar_Syntax_Syntax.NT uu____11175  in
                          [uu____11174]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1617_11198 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1617_11198.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1617_11198.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11199 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11239 =
                  let uu____11246 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11246  in
                (match uu____11239 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11305 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11330 ->
               let uu____11331 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11331 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11627 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11627
       then
         let uu____11632 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11632
       else ());
      (let uu____11638 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____11638
       then
         let uu____11643 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11643
       else ());
      (let uu____11648 = next_prob probs  in
       match uu____11648 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1644_11675 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1644_11675.wl_deferred);
               ctr = (uu___1644_11675.ctr);
               defer_ok = (uu___1644_11675.defer_ok);
               smt_ok = (uu___1644_11675.smt_ok);
               umax_heuristic_ok = (uu___1644_11675.umax_heuristic_ok);
               tcenv = (uu___1644_11675.tcenv);
               wl_implicits = (uu___1644_11675.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11684 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11684
                 then
                   let uu____11687 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11687
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
                       (let uu____11694 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd1
                            probs1
                           in
                        solve env uu____11694)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1656_11700 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1656_11700.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1656_11700.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1656_11700.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1656_11700.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1656_11700.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1656_11700.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1656_11700.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1656_11700.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1656_11700.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11725 ->
                let uu____11735 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11800  ->
                          match uu____11800 with
                          | (c,uu____11810,uu____11811) -> c < probs.ctr))
                   in
                (match uu____11735 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11859 =
                            let uu____11864 =
                              FStar_List.map
                                (fun uu____11885  ->
                                   match uu____11885 with
                                   | (uu____11901,x,y) ->
                                       let uu____11912 = FStar_Thunk.force x
                                          in
                                       (uu____11912, y)) probs.wl_deferred
                               in
                            (uu____11864, (probs.wl_implicits))  in
                          Success uu____11859
                      | uu____11916 ->
                          let uu____11926 =
                            let uu___1674_11927 = probs  in
                            let uu____11928 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11949  ->
                                      match uu____11949 with
                                      | (uu____11957,uu____11958,y) -> y))
                               in
                            {
                              attempting = uu____11928;
                              wl_deferred = rest;
                              ctr = (uu___1674_11927.ctr);
                              defer_ok = (uu___1674_11927.defer_ok);
                              smt_ok = (uu___1674_11927.smt_ok);
                              umax_heuristic_ok =
                                (uu___1674_11927.umax_heuristic_ok);
                              tcenv = (uu___1674_11927.tcenv);
                              wl_implicits = (uu___1674_11927.wl_implicits)
                            }  in
                          solve env uu____11926))))

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
            let uu____11967 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____11967 with
            | USolved wl1 ->
                let uu____11969 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____11969
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____11972 = defer_lit "" orig wl1  in
                solve env uu____11972

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
                  let uu____12023 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12023 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12026 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12039;
                  FStar_Syntax_Syntax.vars = uu____12040;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12043;
                  FStar_Syntax_Syntax.vars = uu____12044;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12057,uu____12058) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12066,FStar_Syntax_Syntax.Tm_uinst uu____12067) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12075 -> USolved wl

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
            ((let uu____12086 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12086
              then
                let uu____12091 = prob_to_string env orig  in
                let uu____12093 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12091 uu____12093
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
               let uu____12186 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12186 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12241 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12241
                then
                  let uu____12246 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12248 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12246 uu____12248
                else ());
               (let uu____12253 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12253 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12299 = eq_prob t1 t2 wl2  in
                         (match uu____12299 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12320 ->
                         let uu____12329 = eq_prob t1 t2 wl2  in
                         (match uu____12329 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12379 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12394 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12395 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12394, uu____12395)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12400 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12401 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12400, uu____12401)
                            in
                         (match uu____12379 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12432 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12432 with
                                | (t1_hd,t1_args) ->
                                    let uu____12477 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12477 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12543 =
                                              let uu____12550 =
                                                let uu____12561 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12561 :: t1_args  in
                                              let uu____12578 =
                                                let uu____12587 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12587 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12636  ->
                                                   fun uu____12637  ->
                                                     fun uu____12638  ->
                                                       match (uu____12636,
                                                               uu____12637,
                                                               uu____12638)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12688),
                                                          (a2,uu____12690))
                                                           ->
                                                           let uu____12727 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12727
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12550
                                                uu____12578
                                               in
                                            match uu____12543 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1828_12753 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1828_12753.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1828_12753.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1828_12753.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12764 =
                                                  solve env1 wl'  in
                                                (match uu____12764 with
                                                 | Success (uu____12767,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1837_12771
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1837_12771.attempting);
                                                            wl_deferred =
                                                              (uu___1837_12771.wl_deferred);
                                                            ctr =
                                                              (uu___1837_12771.ctr);
                                                            defer_ok =
                                                              (uu___1837_12771.defer_ok);
                                                            smt_ok =
                                                              (uu___1837_12771.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1837_12771.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1837_12771.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12772 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12804 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12804 with
                                | (t1_base,p1_opt) ->
                                    let uu____12840 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12840 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____12939 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____12939
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
                                               let uu____12992 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____12992
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
                                               let uu____13024 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13024
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
                                               let uu____13056 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13056
                                           | uu____13059 -> t_base  in
                                         let uu____13076 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13076 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13090 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13090, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13097 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13097 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13133 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13133 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13169 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13169
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
                              let uu____13193 = combine t11 t21 wl2  in
                              (match uu____13193 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13226 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13226
                                     then
                                       let uu____13231 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13231
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13273 ts1 =
               match uu____13273 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13336 = pairwise out t wl2  in
                        (match uu____13336 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13372 =
               let uu____13383 = FStar_List.hd ts  in (uu____13383, [], wl1)
                in
             let uu____13392 = FStar_List.tl ts  in
             aux uu____13372 uu____13392  in
           let uu____13399 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13399 with
           | (this_flex,this_rigid) ->
               let uu____13425 =
                 let uu____13426 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13426.FStar_Syntax_Syntax.n  in
               (match uu____13425 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13451 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13451
                    then
                      let uu____13454 = destruct_flex_t this_flex wl  in
                      (match uu____13454 with
                       | (flex,wl1) ->
                           let uu____13461 = quasi_pattern env flex  in
                           (match uu____13461 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13480 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13480
                                  then
                                    let uu____13485 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13485
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13492 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1939_13495 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1939_13495.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1939_13495.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1939_13495.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1939_13495.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1939_13495.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1939_13495.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1939_13495.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1939_13495.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1939_13495.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13492)
                | uu____13496 ->
                    ((let uu____13498 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13498
                      then
                        let uu____13503 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13503
                      else ());
                     (let uu____13508 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13508 with
                      | (u,_args) ->
                          let uu____13551 =
                            let uu____13552 = FStar_Syntax_Subst.compress u
                               in
                            uu____13552.FStar_Syntax_Syntax.n  in
                          (match uu____13551 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13580 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13580 with
                                 | (u',uu____13599) ->
                                     let uu____13624 =
                                       let uu____13625 = whnf env u'  in
                                       uu____13625.FStar_Syntax_Syntax.n  in
                                     (match uu____13624 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13647 -> false)
                                  in
                               let uu____13649 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13672  ->
                                         match uu___26_13672 with
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
                                              | uu____13686 -> false)
                                         | uu____13690 -> false))
                                  in
                               (match uu____13649 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13705 = whnf env this_rigid
                                         in
                                      let uu____13706 =
                                        FStar_List.collect
                                          (fun uu___27_13712  ->
                                             match uu___27_13712 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13718 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13718]
                                             | uu____13722 -> [])
                                          bounds_probs
                                         in
                                      uu____13705 :: uu____13706  in
                                    let uu____13723 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13723 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13756 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13771 =
                                               let uu____13772 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13772.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13771 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13784 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13784)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13795 -> bound  in
                                           let uu____13796 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13796)  in
                                         (match uu____13756 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13831 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13831
                                                then
                                                  let wl'1 =
                                                    let uu___1999_13837 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___1999_13837.wl_deferred);
                                                      ctr =
                                                        (uu___1999_13837.ctr);
                                                      defer_ok =
                                                        (uu___1999_13837.defer_ok);
                                                      smt_ok =
                                                        (uu___1999_13837.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___1999_13837.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___1999_13837.tcenv);
                                                      wl_implicits =
                                                        (uu___1999_13837.wl_implicits)
                                                    }  in
                                                  let uu____13838 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13838
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13844 =
                                                  solve_t env eq_prob
                                                    (let uu___2004_13846 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2004_13846.wl_deferred);
                                                       ctr =
                                                         (uu___2004_13846.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2004_13846.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2004_13846.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2004_13846.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13844 with
                                                | Success (uu____13848,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2010_13851 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2010_13851.wl_deferred);
                                                        ctr =
                                                          (uu___2010_13851.ctr);
                                                        defer_ok =
                                                          (uu___2010_13851.defer_ok);
                                                        smt_ok =
                                                          (uu___2010_13851.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2010_13851.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2010_13851.tcenv);
                                                        wl_implicits =
                                                          (uu___2010_13851.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2013_13853 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2013_13853.attempting);
                                                        wl_deferred =
                                                          (uu___2013_13853.wl_deferred);
                                                        ctr =
                                                          (uu___2013_13853.ctr);
                                                        defer_ok =
                                                          (uu___2013_13853.defer_ok);
                                                        smt_ok =
                                                          (uu___2013_13853.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2013_13853.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2013_13853.tcenv);
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
                                                    let uu____13869 =
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
                                                    ((let uu____13881 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13881
                                                      then
                                                        let uu____13886 =
                                                          let uu____13888 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13888
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13886
                                                      else ());
                                                     (let uu____13901 =
                                                        let uu____13916 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13916)
                                                         in
                                                      match uu____13901 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____13938))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13964 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13964
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
                                                                  let uu____13984
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____13984))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14009 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14009
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
                                                                    let uu____14029
                                                                    =
                                                                    let uu____14034
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14034
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14029
                                                                    [] wl2
                                                                     in
                                                                  let uu____14040
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14040))))
                                                      | uu____14041 ->
                                                          let uu____14056 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14056 p)))))))
                           | uu____14063 when flip ->
                               let uu____14064 =
                                 let uu____14066 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14068 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14066 uu____14068
                                  in
                               failwith uu____14064
                           | uu____14071 ->
                               let uu____14072 =
                                 let uu____14074 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14076 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14074 uu____14076
                                  in
                               failwith uu____14072)))))

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
                      (fun uu____14112  ->
                         match uu____14112 with
                         | (x,i) ->
                             let uu____14131 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14131, i)) bs_lhs
                     in
                  let uu____14134 = lhs  in
                  match uu____14134 with
                  | (uu____14135,u_lhs,uu____14137) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14234 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14244 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14244, univ)
                             in
                          match uu____14234 with
                          | (k,univ) ->
                              let uu____14251 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14251 with
                               | (uu____14268,u,wl3) ->
                                   let uu____14271 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14271, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14297 =
                              let uu____14310 =
                                let uu____14321 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14321 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14372  ->
                                   fun uu____14373  ->
                                     match (uu____14372, uu____14373) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14474 =
                                           let uu____14481 =
                                             let uu____14484 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14484
                                              in
                                           copy_uvar u_lhs [] uu____14481 wl2
                                            in
                                         (match uu____14474 with
                                          | (uu____14513,t_a,wl3) ->
                                              let uu____14516 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14516 with
                                               | (uu____14535,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14310
                                ([], wl1)
                               in
                            (match uu____14297 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2124_14591 = ct  in
                                   let uu____14592 =
                                     let uu____14595 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14595
                                      in
                                   let uu____14610 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2124_14591.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2124_14591.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14592;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14610;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2124_14591.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2127_14628 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2127_14628.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2127_14628.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14631 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14631 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14669 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14669 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14680 =
                                          let uu____14685 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14685)  in
                                        TERM uu____14680  in
                                      let uu____14686 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14686 with
                                       | (sub_prob,wl3) ->
                                           let uu____14700 =
                                             let uu____14701 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14701
                                              in
                                           solve env uu____14700))
                             | (x,imp)::formals2 ->
                                 let uu____14723 =
                                   let uu____14730 =
                                     let uu____14733 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14733
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14730 wl1
                                    in
                                 (match uu____14723 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14754 =
                                          let uu____14757 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14757
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14754 u_x
                                         in
                                      let uu____14758 =
                                        let uu____14761 =
                                          let uu____14764 =
                                            let uu____14765 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14765, imp)  in
                                          [uu____14764]  in
                                        FStar_List.append bs_terms
                                          uu____14761
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14758 formals2 wl2)
                              in
                           let uu____14792 = occurs_check u_lhs arrow1  in
                           (match uu____14792 with
                            | (uu____14805,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14821 =
                                    FStar_Thunk.mk
                                      (fun uu____14825  ->
                                         let uu____14826 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14826)
                                     in
                                  giveup_or_defer env orig wl uu____14821
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
              (let uu____14859 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14859
               then
                 let uu____14864 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14867 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14864 (rel_to_string (p_rel orig)) uu____14867
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____14998 = rhs wl1 scope env1 subst1  in
                     (match uu____14998 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15021 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15021
                            then
                              let uu____15026 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15026
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15104 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15104 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2197_15106 = hd1  in
                       let uu____15107 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2197_15106.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2197_15106.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15107
                       }  in
                     let hd21 =
                       let uu___2200_15111 = hd2  in
                       let uu____15112 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2200_15111.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2200_15111.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15112
                       }  in
                     let uu____15115 =
                       let uu____15120 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15120
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15115 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15143 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15143
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15150 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15150 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15222 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15222
                                  in
                               ((let uu____15240 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15240
                                 then
                                   let uu____15245 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15247 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15245
                                     uu____15247
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15282 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15318 = aux wl [] env [] bs1 bs2  in
               match uu____15318 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15377 = attempt sub_probs wl2  in
                   solve env1 uu____15377)

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
            let uu___2238_15397 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2238_15397.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2238_15397.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15409 = try_solve env wl'  in
          match uu____15409 with
          | Success (uu____15410,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2247_15414 = wl  in
                  {
                    attempting = (uu___2247_15414.attempting);
                    wl_deferred = (uu___2247_15414.wl_deferred);
                    ctr = (uu___2247_15414.ctr);
                    defer_ok = (uu___2247_15414.defer_ok);
                    smt_ok = (uu___2247_15414.smt_ok);
                    umax_heuristic_ok = (uu___2247_15414.umax_heuristic_ok);
                    tcenv = (uu___2247_15414.tcenv);
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
        (let uu____15423 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15423 wl)

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
              let uu____15437 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15437 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15471 = lhs1  in
              match uu____15471 with
              | (uu____15474,ctx_u,uu____15476) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15484 ->
                        let uu____15485 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15485 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15534 = quasi_pattern env1 lhs1  in
              match uu____15534 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15568) ->
                  let uu____15573 = lhs1  in
                  (match uu____15573 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15588 = occurs_check ctx_u rhs1  in
                       (match uu____15588 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15639 =
                                let uu____15647 =
                                  let uu____15649 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15649
                                   in
                                FStar_Util.Inl uu____15647  in
                              (uu____15639, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15677 =
                                 let uu____15679 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15679  in
                               if uu____15677
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15706 =
                                    let uu____15714 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15714  in
                                  let uu____15720 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15706, uu____15720)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15764 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15764 with
              | (rhs_hd,args) ->
                  let uu____15807 = FStar_Util.prefix args  in
                  (match uu____15807 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15879 = lhs1  in
                       (match uu____15879 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15883 =
                              let uu____15894 =
                                let uu____15901 =
                                  let uu____15904 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15904
                                   in
                                copy_uvar u_lhs [] uu____15901 wl1  in
                              match uu____15894 with
                              | (uu____15931,t_last_arg,wl2) ->
                                  let uu____15934 =
                                    let uu____15941 =
                                      let uu____15942 =
                                        let uu____15951 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____15951]  in
                                      FStar_List.append bs_lhs uu____15942
                                       in
                                    copy_uvar u_lhs uu____15941 t_res_lhs wl2
                                     in
                                  (match uu____15934 with
                                   | (uu____15986,lhs',wl3) ->
                                       let uu____15989 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____15989 with
                                        | (uu____16006,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15883 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16027 =
                                     let uu____16028 =
                                       let uu____16033 =
                                         let uu____16034 =
                                           let uu____16037 =
                                             let uu____16042 =
                                               let uu____16043 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16043]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16042
                                              in
                                           uu____16037
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16034
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16033)  in
                                     TERM uu____16028  in
                                   [uu____16027]  in
                                 let uu____16068 =
                                   let uu____16075 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16075 with
                                   | (p1,wl3) ->
                                       let uu____16095 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16095 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16068 with
                                  | (sub_probs,wl3) ->
                                      let uu____16127 =
                                        let uu____16128 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16128  in
                                      solve env1 uu____16127))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16162 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16162 with
                | (uu____16180,args) ->
                    (match args with | [] -> false | uu____16216 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16235 =
                  let uu____16236 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16236.FStar_Syntax_Syntax.n  in
                match uu____16235 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16240 -> true
                | uu____16256 -> false  in
              let uu____16258 = quasi_pattern env1 lhs1  in
              match uu____16258 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    FStar_Thunk.mk
                      (fun uu____16276  ->
                         let uu____16277 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16277)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16286 = is_app rhs1  in
                  if uu____16286
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16291 = is_arrow rhs1  in
                     if uu____16291
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          FStar_Thunk.mk
                            (fun uu____16303  ->
                               let uu____16304 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16304)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16308 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16308
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16314 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16314
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16319 = lhs  in
                (match uu____16319 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16323 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16323 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16341 =
                              let uu____16345 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16345
                               in
                            FStar_All.pipe_right uu____16341
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16366 = occurs_check ctx_uv rhs1  in
                          (match uu____16366 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16395 =
                                   let uu____16396 =
                                     let uu____16398 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16398
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16396
                                    in
                                 giveup_or_defer env orig wl uu____16395
                               else
                                 (let uu____16406 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16406
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16413 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16413
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         FStar_Thunk.mk
                                           (fun uu____16426  ->
                                              let uu____16427 =
                                                names_to_string1 fvs2  in
                                              let uu____16429 =
                                                names_to_string1 fvs1  in
                                              let uu____16431 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16427 uu____16429
                                                uu____16431)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16443 ->
                          if wl.defer_ok
                          then
                            let uu____16447 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16447
                          else
                            (let uu____16452 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16452 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16478 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16478
                             | (FStar_Util.Inl msg,uu____16480) ->
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
                  let uu____16498 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16498
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16504 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16504
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16526 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16526
                else
                  (let uu____16531 =
                     let uu____16548 = quasi_pattern env lhs  in
                     let uu____16555 = quasi_pattern env rhs  in
                     (uu____16548, uu____16555)  in
                   match uu____16531 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16598 = lhs  in
                       (match uu____16598 with
                        | ({ FStar_Syntax_Syntax.n = uu____16599;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16601;_},u_lhs,uu____16603)
                            ->
                            let uu____16606 = rhs  in
                            (match uu____16606 with
                             | (uu____16607,u_rhs,uu____16609) ->
                                 let uu____16610 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16610
                                 then
                                   let uu____16617 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16617
                                 else
                                   (let uu____16620 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16620 with
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
                                        let uu____16652 =
                                          let uu____16659 =
                                            let uu____16662 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16662
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16659
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16652 with
                                         | (uu____16668,w,wl1) ->
                                             let w_app =
                                               let uu____16674 =
                                                 let uu____16679 =
                                                   FStar_List.map
                                                     (fun uu____16690  ->
                                                        match uu____16690
                                                        with
                                                        | (z,uu____16698) ->
                                                            let uu____16703 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16703) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16679
                                                  in
                                               uu____16674
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16705 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16705
                                               then
                                                 let uu____16710 =
                                                   let uu____16714 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16716 =
                                                     let uu____16720 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16722 =
                                                       let uu____16726 =
                                                         term_to_string w  in
                                                       let uu____16728 =
                                                         let uu____16732 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16741 =
                                                           let uu____16745 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16754 =
                                                             let uu____16758
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16758]
                                                              in
                                                           uu____16745 ::
                                                             uu____16754
                                                            in
                                                         uu____16732 ::
                                                           uu____16741
                                                          in
                                                       uu____16726 ::
                                                         uu____16728
                                                        in
                                                     uu____16720 ::
                                                       uu____16722
                                                      in
                                                   uu____16714 :: uu____16716
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16710
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16775 =
                                                     let uu____16780 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16780)  in
                                                   TERM uu____16775  in
                                                 let uu____16781 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16781
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16789 =
                                                        let uu____16794 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16794)
                                                         in
                                                      TERM uu____16789  in
                                                    [s1; s2])
                                                  in
                                               let uu____16795 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16795))))))
                   | uu____16796 ->
                       let uu____16813 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16813)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16867 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16867
            then
              let uu____16872 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16874 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16876 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16878 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16872 uu____16874 uu____16876 uu____16878
            else ());
           (let uu____16889 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16889 with
            | (head1,args1) ->
                let uu____16932 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____16932 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17002 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17002 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17007 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17007)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17028 =
                         FStar_Thunk.mk
                           (fun uu____17035  ->
                              let uu____17036 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17038 = args_to_string args1  in
                              let uu____17042 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17044 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17036 uu____17038 uu____17042
                                uu____17044)
                          in
                       giveup env1 uu____17028 orig
                     else
                       (let uu____17051 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17056 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17056 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17051
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2503_17060 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2503_17060.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2503_17060.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2503_17060.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2503_17060.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2503_17060.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2503_17060.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2503_17060.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2503_17060.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17070 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17070
                                    else solve env1 wl2))
                        else
                          (let uu____17075 = base_and_refinement env1 t1  in
                           match uu____17075 with
                           | (base1,refinement1) ->
                               let uu____17100 = base_and_refinement env1 t2
                                  in
                               (match uu____17100 with
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
                                           let uu____17265 =
                                             FStar_List.fold_right
                                               (fun uu____17305  ->
                                                  fun uu____17306  ->
                                                    match (uu____17305,
                                                            uu____17306)
                                                    with
                                                    | (((a1,uu____17358),
                                                        (a2,uu____17360)),
                                                       (probs,wl3)) ->
                                                        let uu____17409 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17409
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17265 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17452 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17452
                                                 then
                                                   let uu____17457 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17457
                                                 else ());
                                                (let uu____17463 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17463
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
                                                    (let uu____17490 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17490 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17506 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17506
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17514 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17514))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17539 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17539 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17555 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17555
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17563 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17563)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17591 =
                                           match uu____17591 with
                                           | (prob,reason) ->
                                               ((let uu____17608 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17608
                                                 then
                                                   let uu____17613 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17615 =
                                                     prob_to_string env2 prob
                                                      in
                                                   let uu____17617 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____17613 uu____17615
                                                     uu____17617
                                                 else ());
                                                (let uu____17623 =
                                                   let uu____17632 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17635 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17632, uu____17635)
                                                    in
                                                 match uu____17623 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17648 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17648 with
                                                      | (head1',uu____17666)
                                                          ->
                                                          let uu____17691 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17691
                                                           with
                                                           | (head2',uu____17709)
                                                               ->
                                                               let uu____17734
                                                                 =
                                                                 let uu____17739
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17740
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17739,
                                                                   uu____17740)
                                                                  in
                                                               (match uu____17734
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17742
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17742
                                                                    then
                                                                    let uu____17747
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17749
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17751
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17753
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17747
                                                                    uu____17749
                                                                    uu____17751
                                                                    uu____17753
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17758
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2591_17766
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2591_17766.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2591_17766.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2591_17766.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2591_17766.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2591_17766.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2591_17766.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2591_17766.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2591_17766.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17768
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17768
                                                                    then
                                                                    let uu____17773
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17773
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17778 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17790 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17790 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17798 =
                                             let uu____17799 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17799.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17798 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17804 -> false  in
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
                                          | uu____17807 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17810 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2611_17846 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2611_17846.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2611_17846.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2611_17846.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2611_17846.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2611_17846.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2611_17846.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2611_17846.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2611_17846.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17922 = destruct_flex_t scrutinee wl1  in
             match uu____17922 with
             | ((_t,uv,_args),wl2) ->
                 let uu____17933 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____17933 with
                  | (xs,pat_term,uu____17949,uu____17950) ->
                      let uu____17955 =
                        FStar_List.fold_left
                          (fun uu____17978  ->
                             fun x  ->
                               match uu____17978 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____17999 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____17999 with
                                    | (uu____18018,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____17955 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18039 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18039 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2651_18056 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2651_18056.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2651_18056.umax_heuristic_ok);
                                    tcenv = (uu___2651_18056.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18067 = solve env1 wl'  in
                                (match uu____18067 with
                                 | Success (uu____18070,imps) ->
                                     let wl'1 =
                                       let uu___2659_18073 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2659_18073.wl_deferred);
                                         ctr = (uu___2659_18073.ctr);
                                         defer_ok =
                                           (uu___2659_18073.defer_ok);
                                         smt_ok = (uu___2659_18073.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2659_18073.umax_heuristic_ok);
                                         tcenv = (uu___2659_18073.tcenv);
                                         wl_implicits =
                                           (uu___2659_18073.wl_implicits)
                                       }  in
                                     let uu____18074 = solve env1 wl'1  in
                                     (match uu____18074 with
                                      | Success (uu____18077,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2667_18081 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2667_18081.attempting);
                                                 wl_deferred =
                                                   (uu___2667_18081.wl_deferred);
                                                 ctr = (uu___2667_18081.ctr);
                                                 defer_ok =
                                                   (uu___2667_18081.defer_ok);
                                                 smt_ok =
                                                   (uu___2667_18081.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2667_18081.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2667_18081.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18082 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18088 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18111 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18111
                 then
                   let uu____18116 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18118 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18116 uu____18118
                 else ());
                (let uu____18123 =
                   let uu____18144 =
                     let uu____18153 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18153)  in
                   let uu____18160 =
                     let uu____18169 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18169)  in
                   (uu____18144, uu____18160)  in
                 match uu____18123 with
                 | ((uu____18199,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18202;
                                   FStar_Syntax_Syntax.vars = uu____18203;_}),
                    (s,t)) ->
                     let uu____18274 =
                       let uu____18276 = is_flex scrutinee  in
                       Prims.op_Negation uu____18276  in
                     if uu____18274
                     then
                       ((let uu____18287 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18287
                         then
                           let uu____18292 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18292
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18311 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18311
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18326 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18326
                           then
                             let uu____18331 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18333 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18331 uu____18333
                           else ());
                          (let pat_discriminates uu___28_18358 =
                             match uu___28_18358 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18374;
                                  FStar_Syntax_Syntax.p = uu____18375;_},FStar_Pervasives_Native.None
                                ,uu____18376) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18390;
                                  FStar_Syntax_Syntax.p = uu____18391;_},FStar_Pervasives_Native.None
                                ,uu____18392) -> true
                             | uu____18419 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18522 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18522 with
                                       | (uu____18524,uu____18525,t') ->
                                           let uu____18543 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18543 with
                                            | (FullMatch ,uu____18555) ->
                                                true
                                            | (HeadMatch
                                               uu____18569,uu____18570) ->
                                                true
                                            | uu____18585 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18622 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18622
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18633 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18633 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18721,uu____18722) ->
                                       branches1
                                   | uu____18867 -> branches  in
                                 let uu____18922 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____18931 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____18931 with
                                        | (p,uu____18935,uu____18936) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _18965  -> FStar_Util.Inr _18965)
                                   uu____18922))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18995 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____18995 with
                                | (p,uu____19004,e) ->
                                    ((let uu____19023 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19023
                                      then
                                        let uu____19028 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19030 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19028 uu____19030
                                      else ());
                                     (let uu____19035 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19050  -> FStar_Util.Inr _19050)
                                        uu____19035)))))
                 | ((s,t),(uu____19053,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19056;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19057;_}))
                     ->
                     let uu____19126 =
                       let uu____19128 = is_flex scrutinee  in
                       Prims.op_Negation uu____19128  in
                     if uu____19126
                     then
                       ((let uu____19139 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19139
                         then
                           let uu____19144 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19144
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19163 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19163
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19178 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19178
                           then
                             let uu____19183 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19185 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19183 uu____19185
                           else ());
                          (let pat_discriminates uu___28_19210 =
                             match uu___28_19210 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19226;
                                  FStar_Syntax_Syntax.p = uu____19227;_},FStar_Pervasives_Native.None
                                ,uu____19228) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19242;
                                  FStar_Syntax_Syntax.p = uu____19243;_},FStar_Pervasives_Native.None
                                ,uu____19244) -> true
                             | uu____19271 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19374 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19374 with
                                       | (uu____19376,uu____19377,t') ->
                                           let uu____19395 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19395 with
                                            | (FullMatch ,uu____19407) ->
                                                true
                                            | (HeadMatch
                                               uu____19421,uu____19422) ->
                                                true
                                            | uu____19437 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19474 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19474
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19485 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19485 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19573,uu____19574) ->
                                       branches1
                                   | uu____19719 -> branches  in
                                 let uu____19774 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19783 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19783 with
                                        | (p,uu____19787,uu____19788) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19817  -> FStar_Util.Inr _19817)
                                   uu____19774))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19847 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19847 with
                                | (p,uu____19856,e) ->
                                    ((let uu____19875 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19875
                                      then
                                        let uu____19880 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19882 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19880 uu____19882
                                      else ());
                                     (let uu____19887 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19902  -> FStar_Util.Inr _19902)
                                        uu____19887)))))
                 | uu____19903 ->
                     ((let uu____19925 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19925
                       then
                         let uu____19930 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____19932 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____19930 uu____19932
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____19978 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____19978
            then
              let uu____19983 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____19985 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____19987 = FStar_Syntax_Print.term_to_string t1  in
              let uu____19989 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____19983 uu____19985 uu____19987 uu____19989
            else ());
           (let uu____19994 = head_matches_delta env1 wl1 t1 t2  in
            match uu____19994 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20025,uu____20026) ->
                     let rec may_relate head3 =
                       let uu____20054 =
                         let uu____20055 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20055.FStar_Syntax_Syntax.n  in
                       match uu____20054 with
                       | FStar_Syntax_Syntax.Tm_name uu____20059 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20061 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20086 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20086 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20088 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20091
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20092 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20095,uu____20096) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20138) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20144) ->
                           may_relate t
                       | uu____20149 -> false  in
                     let uu____20151 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20151 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20164 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20164
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20174 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20174
                          then
                            let uu____20177 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20177 with
                             | (guard,wl2) ->
                                 let uu____20184 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20184)
                          else
                            (let uu____20187 =
                               FStar_Thunk.mk
                                 (fun uu____20194  ->
                                    let uu____20195 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20197 =
                                      let uu____20199 =
                                        let uu____20203 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20203
                                          (fun x  ->
                                             let uu____20210 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20210)
                                         in
                                      FStar_Util.dflt "" uu____20199  in
                                    let uu____20215 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20217 =
                                      let uu____20219 =
                                        let uu____20223 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20223
                                          (fun x  ->
                                             let uu____20230 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20230)
                                         in
                                      FStar_Util.dflt "" uu____20219  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20195 uu____20197 uu____20215
                                      uu____20217)
                                in
                             giveup env1 uu____20187 orig))
                 | (HeadMatch (true ),uu____20236) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20251 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20251 with
                        | (guard,wl2) ->
                            let uu____20258 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20258)
                     else
                       (let uu____20261 =
                          FStar_Thunk.mk
                            (fun uu____20266  ->
                               let uu____20267 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20269 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20267 uu____20269)
                           in
                        giveup env1 uu____20261 orig)
                 | (uu____20272,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2842_20286 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2842_20286.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2842_20286.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2842_20286.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2842_20286.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2842_20286.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2842_20286.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2842_20286.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2842_20286.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20313 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20313
          then
            let uu____20316 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20316
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20322 =
                let uu____20325 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20325  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20322 t1);
             (let uu____20344 =
                let uu____20347 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20347  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20344 t2);
             (let uu____20366 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20366
              then
                let uu____20370 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20372 =
                  let uu____20374 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20376 =
                    let uu____20378 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20378  in
                  Prims.op_Hat uu____20374 uu____20376  in
                let uu____20381 =
                  let uu____20383 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20385 =
                    let uu____20387 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20387  in
                  Prims.op_Hat uu____20383 uu____20385  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20370 uu____20372 uu____20381
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20394,uu____20395) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20411,FStar_Syntax_Syntax.Tm_delayed uu____20412) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20428,uu____20429) ->
                  let uu____20456 =
                    let uu___2873_20457 = problem  in
                    let uu____20458 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2873_20457.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20458;
                      FStar_TypeChecker_Common.relation =
                        (uu___2873_20457.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2873_20457.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2873_20457.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2873_20457.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2873_20457.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2873_20457.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2873_20457.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2873_20457.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20456 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20459,uu____20460) ->
                  let uu____20467 =
                    let uu___2879_20468 = problem  in
                    let uu____20469 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2879_20468.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20469;
                      FStar_TypeChecker_Common.relation =
                        (uu___2879_20468.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2879_20468.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2879_20468.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2879_20468.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2879_20468.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2879_20468.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2879_20468.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2879_20468.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20467 wl
              | (uu____20470,FStar_Syntax_Syntax.Tm_ascribed uu____20471) ->
                  let uu____20498 =
                    let uu___2885_20499 = problem  in
                    let uu____20500 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2885_20499.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2885_20499.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2885_20499.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20500;
                      FStar_TypeChecker_Common.element =
                        (uu___2885_20499.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2885_20499.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2885_20499.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2885_20499.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2885_20499.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2885_20499.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20498 wl
              | (uu____20501,FStar_Syntax_Syntax.Tm_meta uu____20502) ->
                  let uu____20509 =
                    let uu___2891_20510 = problem  in
                    let uu____20511 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2891_20510.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2891_20510.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2891_20510.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20511;
                      FStar_TypeChecker_Common.element =
                        (uu___2891_20510.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2891_20510.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2891_20510.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2891_20510.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2891_20510.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2891_20510.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20509 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20513),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20515)) ->
                  let uu____20524 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20524
              | (FStar_Syntax_Syntax.Tm_bvar uu____20525,uu____20526) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20528,FStar_Syntax_Syntax.Tm_bvar uu____20529) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20599 =
                    match uu___29_20599 with
                    | [] -> c
                    | bs ->
                        let uu____20627 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20627
                     in
                  let uu____20638 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20638 with
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
                                    let uu____20787 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20787
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
                  let mk_t t l uu___30_20876 =
                    match uu___30_20876 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____20918 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____20918 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21063 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21064 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21063
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21064 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21066,uu____21067) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21098 -> true
                    | uu____21118 -> false  in
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
                      (let uu____21178 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2993_21186 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2993_21186.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2993_21186.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2993_21186.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2993_21186.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2993_21186.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2993_21186.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2993_21186.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2993_21186.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2993_21186.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2993_21186.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2993_21186.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2993_21186.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2993_21186.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2993_21186.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2993_21186.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2993_21186.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___2993_21186.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2993_21186.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2993_21186.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2993_21186.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2993_21186.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2993_21186.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2993_21186.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2993_21186.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2993_21186.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2993_21186.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2993_21186.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2993_21186.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2993_21186.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2993_21186.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2993_21186.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2993_21186.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2993_21186.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2993_21186.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2993_21186.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___2993_21186.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2993_21186.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2993_21186.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2993_21186.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2993_21186.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2993_21186.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2993_21186.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2993_21186.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2993_21186.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21178 with
                       | (uu____21191,ty,uu____21193) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21202 =
                                 let uu____21203 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21203.FStar_Syntax_Syntax.n  in
                               match uu____21202 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21206 ->
                                   let uu____21213 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21213
                               | uu____21214 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21217 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21217
                             then
                               let uu____21222 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21224 =
                                 let uu____21226 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21226
                                  in
                               let uu____21227 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21222 uu____21224 uu____21227
                             else ());
                            r1))
                     in
                  let uu____21232 =
                    let uu____21249 = maybe_eta t1  in
                    let uu____21256 = maybe_eta t2  in
                    (uu____21249, uu____21256)  in
                  (match uu____21232 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3014_21298 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3014_21298.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3014_21298.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3014_21298.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3014_21298.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3014_21298.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3014_21298.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3014_21298.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3014_21298.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21319 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21319
                       then
                         let uu____21322 = destruct_flex_t not_abs wl  in
                         (match uu____21322 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21339 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21339.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21339.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21339.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21339.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21339.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21339.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21339.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21339.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21342 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21342 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21365 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21365
                       then
                         let uu____21368 = destruct_flex_t not_abs wl  in
                         (match uu____21368 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21385 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21385.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21385.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21385.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21385.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21385.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21385.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21385.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21385.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21388 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21388 orig))
                   | uu____21391 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21409,FStar_Syntax_Syntax.Tm_abs uu____21410) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21441 -> true
                    | uu____21461 -> false  in
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
                      (let uu____21521 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2993_21529 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2993_21529.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2993_21529.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2993_21529.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2993_21529.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2993_21529.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2993_21529.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2993_21529.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2993_21529.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2993_21529.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2993_21529.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2993_21529.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2993_21529.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2993_21529.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2993_21529.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2993_21529.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2993_21529.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___2993_21529.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2993_21529.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2993_21529.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2993_21529.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2993_21529.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2993_21529.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2993_21529.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2993_21529.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2993_21529.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2993_21529.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2993_21529.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2993_21529.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2993_21529.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2993_21529.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2993_21529.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2993_21529.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2993_21529.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2993_21529.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2993_21529.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___2993_21529.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2993_21529.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2993_21529.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2993_21529.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2993_21529.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2993_21529.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2993_21529.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2993_21529.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2993_21529.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21521 with
                       | (uu____21534,ty,uu____21536) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21545 =
                                 let uu____21546 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21546.FStar_Syntax_Syntax.n  in
                               match uu____21545 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21549 ->
                                   let uu____21556 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21556
                               | uu____21557 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21560 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21560
                             then
                               let uu____21565 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21567 =
                                 let uu____21569 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21569
                                  in
                               let uu____21570 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21565 uu____21567 uu____21570
                             else ());
                            r1))
                     in
                  let uu____21575 =
                    let uu____21592 = maybe_eta t1  in
                    let uu____21599 = maybe_eta t2  in
                    (uu____21592, uu____21599)  in
                  (match uu____21575 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3014_21641 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3014_21641.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3014_21641.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3014_21641.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3014_21641.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3014_21641.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3014_21641.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3014_21641.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3014_21641.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21662 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21662
                       then
                         let uu____21665 = destruct_flex_t not_abs wl  in
                         (match uu____21665 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21682 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21682.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21682.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21682.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21682.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21682.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21682.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21682.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21682.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21685 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21685 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21708 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21708
                       then
                         let uu____21711 = destruct_flex_t not_abs wl  in
                         (match uu____21711 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21728 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21728.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21728.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21728.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21728.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21728.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21728.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21728.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21728.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21731 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21731 orig))
                   | uu____21734 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21764 =
                    let uu____21769 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21769 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3054_21797 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3054_21797.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3054_21797.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3056_21799 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3056_21799.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3056_21799.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21800,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3054_21815 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3054_21815.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3054_21815.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3056_21817 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3056_21817.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3056_21817.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21818 -> (x1, x2)  in
                  (match uu____21764 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21837 = as_refinement false env t11  in
                       (match uu____21837 with
                        | (x12,phi11) ->
                            let uu____21845 = as_refinement false env t21  in
                            (match uu____21845 with
                             | (x22,phi21) ->
                                 ((let uu____21854 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21854
                                   then
                                     ((let uu____21859 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21861 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21863 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21859
                                         uu____21861 uu____21863);
                                      (let uu____21866 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21868 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21870 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21866
                                         uu____21868 uu____21870))
                                   else ());
                                  (let uu____21875 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21875 with
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
                                         let uu____21946 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____21946
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____21958 =
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
                                         (let uu____21971 =
                                            let uu____21974 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21974
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____21971
                                            (p_guard base_prob));
                                         (let uu____21993 =
                                            let uu____21996 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21996
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____21993
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22015 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22015)
                                          in
                                       let has_uvars =
                                         (let uu____22020 =
                                            let uu____22022 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22022
                                             in
                                          Prims.op_Negation uu____22020) ||
                                           (let uu____22026 =
                                              let uu____22028 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22028
                                               in
                                            Prims.op_Negation uu____22026)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22032 =
                                           let uu____22037 =
                                             let uu____22046 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22046]  in
                                           mk_t_problem wl1 uu____22037 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22032 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22069 =
                                                solve env1
                                                  (let uu___3099_22071 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3099_22071.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3099_22071.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3099_22071.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3099_22071.tcenv);
                                                     wl_implicits =
                                                       (uu___3099_22071.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22069 with
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
                                               | Success uu____22086 ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22095 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22095
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3112_22104 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3112_22104.attempting);
                                                         wl_deferred =
                                                           (uu___3112_22104.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3112_22104.defer_ok);
                                                         smt_ok =
                                                           (uu___3112_22104.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3112_22104.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3112_22104.tcenv);
                                                         wl_implicits =
                                                           (uu___3112_22104.wl_implicits)
                                                       }  in
                                                     let uu____22106 =
                                                       attempt [base_prob]
                                                         wl4
                                                        in
                                                     solve env1 uu____22106))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22109,FStar_Syntax_Syntax.Tm_uvar uu____22110) ->
                  let uu____22135 = destruct_flex_t t1 wl  in
                  (match uu____22135 with
                   | (f1,wl1) ->
                       let uu____22142 = destruct_flex_t t2 wl1  in
                       (match uu____22142 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22149;
                    FStar_Syntax_Syntax.pos = uu____22150;
                    FStar_Syntax_Syntax.vars = uu____22151;_},uu____22152),FStar_Syntax_Syntax.Tm_uvar
                 uu____22153) ->
                  let uu____22202 = destruct_flex_t t1 wl  in
                  (match uu____22202 with
                   | (f1,wl1) ->
                       let uu____22209 = destruct_flex_t t2 wl1  in
                       (match uu____22209 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22216,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22217;
                    FStar_Syntax_Syntax.pos = uu____22218;
                    FStar_Syntax_Syntax.vars = uu____22219;_},uu____22220))
                  ->
                  let uu____22269 = destruct_flex_t t1 wl  in
                  (match uu____22269 with
                   | (f1,wl1) ->
                       let uu____22276 = destruct_flex_t t2 wl1  in
                       (match uu____22276 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22283;
                    FStar_Syntax_Syntax.pos = uu____22284;
                    FStar_Syntax_Syntax.vars = uu____22285;_},uu____22286),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22287;
                    FStar_Syntax_Syntax.pos = uu____22288;
                    FStar_Syntax_Syntax.vars = uu____22289;_},uu____22290))
                  ->
                  let uu____22363 = destruct_flex_t t1 wl  in
                  (match uu____22363 with
                   | (f1,wl1) ->
                       let uu____22370 = destruct_flex_t t2 wl1  in
                       (match uu____22370 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22377,uu____22378) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22391 = destruct_flex_t t1 wl  in
                  (match uu____22391 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22398;
                    FStar_Syntax_Syntax.pos = uu____22399;
                    FStar_Syntax_Syntax.vars = uu____22400;_},uu____22401),uu____22402)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22439 = destruct_flex_t t1 wl  in
                  (match uu____22439 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22446,FStar_Syntax_Syntax.Tm_uvar uu____22447) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22460,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22461;
                    FStar_Syntax_Syntax.pos = uu____22462;
                    FStar_Syntax_Syntax.vars = uu____22463;_},uu____22464))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22501,FStar_Syntax_Syntax.Tm_arrow uu____22502) ->
                  solve_t' env
                    (let uu___3212_22530 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3212_22530.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3212_22530.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3212_22530.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3212_22530.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3212_22530.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3212_22530.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3212_22530.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3212_22530.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3212_22530.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22531;
                    FStar_Syntax_Syntax.pos = uu____22532;
                    FStar_Syntax_Syntax.vars = uu____22533;_},uu____22534),FStar_Syntax_Syntax.Tm_arrow
                 uu____22535) ->
                  solve_t' env
                    (let uu___3212_22587 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3212_22587.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3212_22587.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3212_22587.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3212_22587.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3212_22587.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3212_22587.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3212_22587.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3212_22587.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3212_22587.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22588,FStar_Syntax_Syntax.Tm_uvar uu____22589) ->
                  let uu____22602 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22602
              | (uu____22603,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22604;
                    FStar_Syntax_Syntax.pos = uu____22605;
                    FStar_Syntax_Syntax.vars = uu____22606;_},uu____22607))
                  ->
                  let uu____22644 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22644
              | (FStar_Syntax_Syntax.Tm_uvar uu____22645,uu____22646) ->
                  let uu____22659 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22659
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22660;
                    FStar_Syntax_Syntax.pos = uu____22661;
                    FStar_Syntax_Syntax.vars = uu____22662;_},uu____22663),uu____22664)
                  ->
                  let uu____22701 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22701
              | (FStar_Syntax_Syntax.Tm_refine uu____22702,uu____22703) ->
                  let t21 =
                    let uu____22711 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22711  in
                  solve_t env
                    (let uu___3247_22737 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3247_22737.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3247_22737.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3247_22737.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3247_22737.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3247_22737.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3247_22737.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3247_22737.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3247_22737.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3247_22737.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22738,FStar_Syntax_Syntax.Tm_refine uu____22739) ->
                  let t11 =
                    let uu____22747 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22747  in
                  solve_t env
                    (let uu___3254_22773 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3254_22773.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3254_22773.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3254_22773.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3254_22773.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3254_22773.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3254_22773.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3254_22773.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3254_22773.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3254_22773.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22855 =
                    let uu____22856 = guard_of_prob env wl problem t1 t2  in
                    match uu____22856 with
                    | (guard,wl1) ->
                        let uu____22863 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22863
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23082 = br1  in
                        (match uu____23082 with
                         | (p1,w1,uu____23111) ->
                             let uu____23128 = br2  in
                             (match uu____23128 with
                              | (p2,w2,uu____23151) ->
                                  let uu____23156 =
                                    let uu____23158 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23158  in
                                  if uu____23156
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23185 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23185 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23222 = br2  in
                                         (match uu____23222 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23255 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23255
                                                 in
                                              let uu____23260 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23291,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23312) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23371 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23371 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23260
                                                (fun uu____23443  ->
                                                   match uu____23443 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23480 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23480
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23501
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23501
                                                              then
                                                                let uu____23506
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23508
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23506
                                                                  uu____23508
                                                              else ());
                                                             (let uu____23514
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23514
                                                                (fun
                                                                   uu____23550
                                                                    ->
                                                                   match uu____23550
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
                    | uu____23679 -> FStar_Pervasives_Native.None  in
                  let uu____23720 = solve_branches wl brs1 brs2  in
                  (match uu____23720 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23746 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23746 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23773 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23773 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23807 =
                                FStar_List.map
                                  (fun uu____23819  ->
                                     match uu____23819 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23807  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23828 =
                              let uu____23829 =
                                let uu____23830 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23830
                                  (let uu___3353_23838 = wl3  in
                                   {
                                     attempting =
                                       (uu___3353_23838.attempting);
                                     wl_deferred =
                                       (uu___3353_23838.wl_deferred);
                                     ctr = (uu___3353_23838.ctr);
                                     defer_ok = (uu___3353_23838.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3353_23838.umax_heuristic_ok);
                                     tcenv = (uu___3353_23838.tcenv);
                                     wl_implicits =
                                       (uu___3353_23838.wl_implicits)
                                   })
                                 in
                              solve env uu____23829  in
                            (match uu____23828 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23843 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____23852 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____23852 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____23855,uu____23856) ->
                  let head1 =
                    let uu____23880 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23880
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23926 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23926
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23972 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23972
                    then
                      let uu____23976 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23978 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23980 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23976 uu____23978 uu____23980
                    else ());
                   (let no_free_uvars t =
                      (let uu____23994 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23994) &&
                        (let uu____23998 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23998)
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
                      let uu____24017 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24017 = FStar_Syntax_Util.Equal  in
                    let uu____24018 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24018
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24022 = equal t1 t2  in
                         (if uu____24022
                          then
                            let uu____24025 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24025
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24030 =
                            let uu____24037 = equal t1 t2  in
                            if uu____24037
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24050 = mk_eq2 wl env orig t1 t2  in
                               match uu____24050 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24030 with
                          | (guard,wl1) ->
                              let uu____24071 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24071))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24074,uu____24075) ->
                  let head1 =
                    let uu____24083 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24083
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24129 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24129
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24175 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24175
                    then
                      let uu____24179 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24181 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24183 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24179 uu____24181 uu____24183
                    else ());
                   (let no_free_uvars t =
                      (let uu____24197 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24197) &&
                        (let uu____24201 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24201)
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
                      let uu____24220 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24220 = FStar_Syntax_Util.Equal  in
                    let uu____24221 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24221
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24225 = equal t1 t2  in
                         (if uu____24225
                          then
                            let uu____24228 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24228
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24233 =
                            let uu____24240 = equal t1 t2  in
                            if uu____24240
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24253 = mk_eq2 wl env orig t1 t2  in
                               match uu____24253 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24233 with
                          | (guard,wl1) ->
                              let uu____24274 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24274))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24277,uu____24278) ->
                  let head1 =
                    let uu____24280 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24280
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24326 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24326
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24372 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24372
                    then
                      let uu____24376 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24378 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24380 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24376 uu____24378 uu____24380
                    else ());
                   (let no_free_uvars t =
                      (let uu____24394 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24394) &&
                        (let uu____24398 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24398)
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
                      let uu____24417 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24417 = FStar_Syntax_Util.Equal  in
                    let uu____24418 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24418
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24422 = equal t1 t2  in
                         (if uu____24422
                          then
                            let uu____24425 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24425
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24430 =
                            let uu____24437 = equal t1 t2  in
                            if uu____24437
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24450 = mk_eq2 wl env orig t1 t2  in
                               match uu____24450 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24430 with
                          | (guard,wl1) ->
                              let uu____24471 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24471))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24474,uu____24475) ->
                  let head1 =
                    let uu____24477 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24477
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24523 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24523
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24569 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24569
                    then
                      let uu____24573 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24575 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24577 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24573 uu____24575 uu____24577
                    else ());
                   (let no_free_uvars t =
                      (let uu____24591 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24591) &&
                        (let uu____24595 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24595)
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
                      let uu____24614 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24614 = FStar_Syntax_Util.Equal  in
                    let uu____24615 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24615
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24619 = equal t1 t2  in
                         (if uu____24619
                          then
                            let uu____24622 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24622
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24627 =
                            let uu____24634 = equal t1 t2  in
                            if uu____24634
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24647 = mk_eq2 wl env orig t1 t2  in
                               match uu____24647 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24627 with
                          | (guard,wl1) ->
                              let uu____24668 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24668))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24671,uu____24672) ->
                  let head1 =
                    let uu____24674 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24674
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24720 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24720
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24766 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24766
                    then
                      let uu____24770 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24772 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24774 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24770 uu____24772 uu____24774
                    else ());
                   (let no_free_uvars t =
                      (let uu____24788 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24788) &&
                        (let uu____24792 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24792)
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
                      let uu____24811 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24811 = FStar_Syntax_Util.Equal  in
                    let uu____24812 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24812
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24816 = equal t1 t2  in
                         (if uu____24816
                          then
                            let uu____24819 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24819
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24824 =
                            let uu____24831 = equal t1 t2  in
                            if uu____24831
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24844 = mk_eq2 wl env orig t1 t2  in
                               match uu____24844 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24824 with
                          | (guard,wl1) ->
                              let uu____24865 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24865))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24868,uu____24869) ->
                  let head1 =
                    let uu____24887 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24887
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24933 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24933
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24979 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24979
                    then
                      let uu____24983 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24985 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24987 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24983 uu____24985 uu____24987
                    else ());
                   (let no_free_uvars t =
                      (let uu____25001 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25001) &&
                        (let uu____25005 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25005)
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
                      let uu____25024 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25024 = FStar_Syntax_Util.Equal  in
                    let uu____25025 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25025
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25029 = equal t1 t2  in
                         (if uu____25029
                          then
                            let uu____25032 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25032
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25037 =
                            let uu____25044 = equal t1 t2  in
                            if uu____25044
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25057 = mk_eq2 wl env orig t1 t2  in
                               match uu____25057 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25037 with
                          | (guard,wl1) ->
                              let uu____25078 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25078))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25081,FStar_Syntax_Syntax.Tm_match uu____25082) ->
                  let head1 =
                    let uu____25106 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25106
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25152 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25152
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25198 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25198
                    then
                      let uu____25202 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25204 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25206 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25202 uu____25204 uu____25206
                    else ());
                   (let no_free_uvars t =
                      (let uu____25220 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25220) &&
                        (let uu____25224 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25224)
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
                      let uu____25243 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25243 = FStar_Syntax_Util.Equal  in
                    let uu____25244 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25244
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25248 = equal t1 t2  in
                         (if uu____25248
                          then
                            let uu____25251 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25251
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25256 =
                            let uu____25263 = equal t1 t2  in
                            if uu____25263
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25276 = mk_eq2 wl env orig t1 t2  in
                               match uu____25276 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25256 with
                          | (guard,wl1) ->
                              let uu____25297 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25297))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25300,FStar_Syntax_Syntax.Tm_uinst uu____25301) ->
                  let head1 =
                    let uu____25309 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25309
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25355 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25355
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25401 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25401
                    then
                      let uu____25405 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25407 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25409 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25405 uu____25407 uu____25409
                    else ());
                   (let no_free_uvars t =
                      (let uu____25423 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25423) &&
                        (let uu____25427 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25427)
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
                      let uu____25446 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25446 = FStar_Syntax_Util.Equal  in
                    let uu____25447 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25447
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25451 = equal t1 t2  in
                         (if uu____25451
                          then
                            let uu____25454 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25454
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25459 =
                            let uu____25466 = equal t1 t2  in
                            if uu____25466
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25479 = mk_eq2 wl env orig t1 t2  in
                               match uu____25479 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25459 with
                          | (guard,wl1) ->
                              let uu____25500 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25500))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25503,FStar_Syntax_Syntax.Tm_name uu____25504) ->
                  let head1 =
                    let uu____25506 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25506
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25552 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25552
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25592 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25592
                    then
                      let uu____25596 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25598 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25600 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25596 uu____25598 uu____25600
                    else ());
                   (let no_free_uvars t =
                      (let uu____25614 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25614) &&
                        (let uu____25618 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25618)
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
                      let uu____25637 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25637 = FStar_Syntax_Util.Equal  in
                    let uu____25638 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25638
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25642 = equal t1 t2  in
                         (if uu____25642
                          then
                            let uu____25645 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25645
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25650 =
                            let uu____25657 = equal t1 t2  in
                            if uu____25657
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25670 = mk_eq2 wl env orig t1 t2  in
                               match uu____25670 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25650 with
                          | (guard,wl1) ->
                              let uu____25691 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25691))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25694,FStar_Syntax_Syntax.Tm_constant uu____25695) ->
                  let head1 =
                    let uu____25697 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25697
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25737 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25737
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25777 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25777
                    then
                      let uu____25781 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25783 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25785 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25781 uu____25783 uu____25785
                    else ());
                   (let no_free_uvars t =
                      (let uu____25799 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25799) &&
                        (let uu____25803 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25803)
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
                      let uu____25822 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25822 = FStar_Syntax_Util.Equal  in
                    let uu____25823 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25823
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25827 = equal t1 t2  in
                         (if uu____25827
                          then
                            let uu____25830 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25830
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25835 =
                            let uu____25842 = equal t1 t2  in
                            if uu____25842
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25855 = mk_eq2 wl env orig t1 t2  in
                               match uu____25855 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25835 with
                          | (guard,wl1) ->
                              let uu____25876 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25876))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25879,FStar_Syntax_Syntax.Tm_fvar uu____25880) ->
                  let head1 =
                    let uu____25882 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25882
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25928 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25928
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25974 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25974
                    then
                      let uu____25978 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25980 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25982 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25978 uu____25980 uu____25982
                    else ());
                   (let no_free_uvars t =
                      (let uu____25996 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25996) &&
                        (let uu____26000 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26000)
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
                      let uu____26019 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26019 = FStar_Syntax_Util.Equal  in
                    let uu____26020 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26020
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26024 = equal t1 t2  in
                         (if uu____26024
                          then
                            let uu____26027 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26027
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26032 =
                            let uu____26039 = equal t1 t2  in
                            if uu____26039
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26052 = mk_eq2 wl env orig t1 t2  in
                               match uu____26052 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26032 with
                          | (guard,wl1) ->
                              let uu____26073 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26073))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26076,FStar_Syntax_Syntax.Tm_app uu____26077) ->
                  let head1 =
                    let uu____26095 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26095
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26135 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26135
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26175 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26175
                    then
                      let uu____26179 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26181 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26183 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26179 uu____26181 uu____26183
                    else ());
                   (let no_free_uvars t =
                      (let uu____26197 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26197) &&
                        (let uu____26201 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26201)
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
                      let uu____26220 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26220 = FStar_Syntax_Util.Equal  in
                    let uu____26221 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26221
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26225 = equal t1 t2  in
                         (if uu____26225
                          then
                            let uu____26228 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26228
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26233 =
                            let uu____26240 = equal t1 t2  in
                            if uu____26240
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26253 = mk_eq2 wl env orig t1 t2  in
                               match uu____26253 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26233 with
                          | (guard,wl1) ->
                              let uu____26274 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26274))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26277,FStar_Syntax_Syntax.Tm_let uu____26278) ->
                  let uu____26305 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26305
                  then
                    let uu____26308 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26308
                  else
                    (let uu____26311 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26311 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26314,uu____26315) ->
                  let uu____26329 =
                    let uu____26335 =
                      let uu____26337 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26339 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26341 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26343 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26337 uu____26339 uu____26341 uu____26343
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26335)
                     in
                  FStar_Errors.raise_error uu____26329
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26347,FStar_Syntax_Syntax.Tm_let uu____26348) ->
                  let uu____26362 =
                    let uu____26368 =
                      let uu____26370 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26372 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26374 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26376 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26370 uu____26372 uu____26374 uu____26376
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26368)
                     in
                  FStar_Errors.raise_error uu____26362
                    t1.FStar_Syntax_Syntax.pos
              | uu____26380 ->
                  let uu____26385 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26385 orig))))

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
          (let uu____26451 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26451
           then
             let uu____26456 =
               let uu____26458 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26458  in
             let uu____26459 =
               let uu____26461 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26461  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26456 uu____26459
           else ());
          (let uu____26465 =
             let uu____26467 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26467  in
           if uu____26465
           then
             let uu____26470 =
               FStar_Thunk.mk
                 (fun uu____26475  ->
                    let uu____26476 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26478 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26476 uu____26478)
                in
             giveup env uu____26470 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26500 =
                  FStar_Thunk.mk
                    (fun uu____26505  ->
                       let uu____26506 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26508 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26506 uu____26508)
                   in
                giveup env uu____26500 orig)
             else
               (let uu____26513 =
                  FStar_List.fold_left2
                    (fun uu____26534  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26534 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26555 =
                                 let uu____26560 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26561 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26560
                                   FStar_TypeChecker_Common.EQ uu____26561
                                   "effect universes"
                                  in
                               (match uu____26555 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26513 with
                | (univ_sub_probs,wl1) ->
                    let uu____26581 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26581 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26589 =
                           FStar_List.fold_right2
                             (fun uu____26626  ->
                                fun uu____26627  ->
                                  fun uu____26628  ->
                                    match (uu____26626, uu____26627,
                                            uu____26628)
                                    with
                                    | ((a1,uu____26672),(a2,uu____26674),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26707 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26707 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26589 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26734 =
                                  let uu____26737 =
                                    let uu____26740 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26740
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26737
                                   in
                                FStar_List.append univ_sub_probs uu____26734
                                 in
                              let guard =
                                let guard =
                                  let uu____26762 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26762  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3505_26771 = wl3  in
                                {
                                  attempting = (uu___3505_26771.attempting);
                                  wl_deferred = (uu___3505_26771.wl_deferred);
                                  ctr = (uu___3505_26771.ctr);
                                  defer_ok = (uu___3505_26771.defer_ok);
                                  smt_ok = (uu___3505_26771.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3505_26771.umax_heuristic_ok);
                                  tcenv = (uu___3505_26771.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26773 = attempt sub_probs wl5  in
                              solve env uu____26773))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26791 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26791
           then
             let uu____26796 =
               let uu____26798 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26798
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26800 =
               let uu____26802 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26802
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26796 uu____26800
           else ());
          (let uu____26807 =
             let uu____26812 =
               let uu____26817 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26817
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26812
               (fun uu____26834  ->
                  match uu____26834 with
                  | (c,g) ->
                      let uu____26845 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26845, g))
              in
           match uu____26807 with
           | (c12,g_lift) ->
               ((let uu____26849 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26849
                 then
                   let uu____26854 =
                     let uu____26856 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26856
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26858 =
                     let uu____26860 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26860
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26854 uu____26858
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3525_26870 = wl  in
                     {
                       attempting = (uu___3525_26870.attempting);
                       wl_deferred = (uu___3525_26870.wl_deferred);
                       ctr = (uu___3525_26870.ctr);
                       defer_ok = (uu___3525_26870.defer_ok);
                       smt_ok = (uu___3525_26870.smt_ok);
                       umax_heuristic_ok =
                         (uu___3525_26870.umax_heuristic_ok);
                       tcenv = (uu___3525_26870.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26871 =
                     let rec is_uvar1 t =
                       let uu____26885 =
                         let uu____26886 = FStar_Syntax_Subst.compress t  in
                         uu____26886.FStar_Syntax_Syntax.n  in
                       match uu____26885 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26890 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____26905) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____26911) ->
                           is_uvar1 t1
                       | uu____26936 -> false  in
                     FStar_List.fold_right2
                       (fun uu____26970  ->
                          fun uu____26971  ->
                            fun uu____26972  ->
                              match (uu____26970, uu____26971, uu____26972)
                              with
                              | ((a1,uu____27016),(a2,uu____27018),(is_sub_probs,wl2))
                                  ->
                                  let uu____27051 = is_uvar1 a1  in
                                  if uu____27051
                                  then
                                    ((let uu____27061 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27061
                                      then
                                        let uu____27066 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27068 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27066 uu____27068
                                      else ());
                                     (let uu____27073 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27073 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26871 with
                   | (is_sub_probs,wl2) ->
                       let uu____27101 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27101 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27109 =
                              let uu____27114 =
                                let uu____27115 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27115
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27114
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27109 with
                             | (uu____27122,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27133 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27135 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27133 s uu____27135
                                    in
                                 let uu____27138 =
                                   let uu____27167 =
                                     let uu____27168 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27168.FStar_Syntax_Syntax.n  in
                                   match uu____27167 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27228 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27228 with
                                        | (a::bs1,c3) ->
                                            let uu____27284 =
                                              let uu____27303 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27303
                                                (fun uu____27407  ->
                                                   match uu____27407 with
                                                   | (l1,l2) ->
                                                       let uu____27480 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27480))
                                               in
                                            (match uu____27284 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27585 ->
                                       let uu____27586 =
                                         let uu____27592 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27592)
                                          in
                                       FStar_Errors.raise_error uu____27586 r
                                    in
                                 (match uu____27138 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27668 =
                                        let uu____27675 =
                                          let uu____27676 =
                                            let uu____27677 =
                                              let uu____27684 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27684,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27677
                                             in
                                          [uu____27676]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27675
                                          (fun b  ->
                                             let uu____27700 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27702 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27704 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27700 uu____27702
                                               uu____27704) r
                                         in
                                      (match uu____27668 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27714 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27714
                                             then
                                               let uu____27719 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27728 =
                                                          let uu____27730 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27730
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27728) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27719
                                             else ());
                                            (let wl4 =
                                               let uu___3597_27738 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3597_27738.attempting);
                                                 wl_deferred =
                                                   (uu___3597_27738.wl_deferred);
                                                 ctr = (uu___3597_27738.ctr);
                                                 defer_ok =
                                                   (uu___3597_27738.defer_ok);
                                                 smt_ok =
                                                   (uu___3597_27738.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3597_27738.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3597_27738.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27763 =
                                                        let uu____27770 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27770, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27763) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27787 =
                                               let f_sort_is =
                                                 let uu____27797 =
                                                   let uu____27798 =
                                                     let uu____27801 =
                                                       let uu____27802 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27802.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27801
                                                      in
                                                   uu____27798.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27797 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27813,uu____27814::is)
                                                     ->
                                                     let uu____27856 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____27856
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____27889 ->
                                                     let uu____27890 =
                                                       let uu____27896 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____27896)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____27890 r
                                                  in
                                               let uu____27902 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____27937  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____27937
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____27958 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____27958
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____27902
                                                in
                                             match uu____27787 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____27983 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____27983
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____27984 =
                                                   let g_sort_is =
                                                     let uu____27994 =
                                                       let uu____27995 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____27995.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____27994 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28000,uu____28001::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28061 ->
                                                         let uu____28062 =
                                                           let uu____28068 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28068)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28062 r
                                                      in
                                                   let uu____28074 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28109  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28109
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28130
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28130
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28074
                                                    in
                                                 (match uu____27984 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28157 =
                                                          let uu____28162 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28163 =
                                                            let uu____28164 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28164
                                                             in
                                                          (uu____28162,
                                                            uu____28163)
                                                           in
                                                        match uu____28157
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28192 =
                                                          let uu____28195 =
                                                            let uu____28198 =
                                                              let uu____28201
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28201
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28198
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28195
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28192
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28225 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28225
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
                                                        let uu____28236 =
                                                          let uu____28239 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28242  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28242)
                                                            uu____28239
                                                           in
                                                        solve_prob orig
                                                          uu____28236 [] wl6
                                                         in
                                                      let uu____28243 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28243))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28266 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28268 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28268]
              | x -> x  in
            let c12 =
              let uu___3663_28271 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3663_28271.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3663_28271.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3663_28271.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3663_28271.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28272 =
              let uu____28277 =
                FStar_All.pipe_right
                  (let uu___3666_28279 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3666_28279.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3666_28279.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3666_28279.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3666_28279.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28277
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28272
              (fun uu____28293  ->
                 match uu____28293 with
                 | (c,g) ->
                     let uu____28300 =
                       let uu____28302 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28302  in
                     if uu____28300
                     then
                       let uu____28305 =
                         let uu____28311 =
                           let uu____28313 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28315 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28313 uu____28315
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28311)
                          in
                       FStar_Errors.raise_error uu____28305 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28321 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28321
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28327 = lift_c1 ()  in
               solve_eq uu____28327 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28336  ->
                         match uu___31_28336 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28341 -> false))
                  in
               let uu____28343 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28373)::uu____28374,(wp2,uu____28376)::uu____28377)
                     -> (wp1, wp2)
                 | uu____28450 ->
                     let uu____28475 =
                       let uu____28481 =
                         let uu____28483 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28485 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28483 uu____28485
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28481)
                        in
                     FStar_Errors.raise_error uu____28475
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28343 with
               | (wpc1,wpc2) ->
                   let uu____28495 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28495
                   then
                     let uu____28498 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28498 wl
                   else
                     (let uu____28502 =
                        let uu____28509 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28509  in
                      match uu____28502 with
                      | (c2_decl,qualifiers) ->
                          let uu____28530 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28530
                          then
                            let c1_repr =
                              let uu____28537 =
                                let uu____28538 =
                                  let uu____28539 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28539  in
                                let uu____28540 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28538 uu____28540
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28537
                               in
                            let c2_repr =
                              let uu____28543 =
                                let uu____28544 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28545 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28544 uu____28545
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28543
                               in
                            let uu____28547 =
                              let uu____28552 =
                                let uu____28554 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28556 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28554
                                  uu____28556
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28552
                               in
                            (match uu____28547 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28562 = attempt [prob] wl2  in
                                 solve env uu____28562)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28582 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28582
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28605 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28605
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
                                        let uu____28615 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28615 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28622 =
                                        let uu____28629 =
                                          let uu____28630 =
                                            let uu____28647 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28650 =
                                              let uu____28661 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28661; wpc1_2]  in
                                            (uu____28647, uu____28650)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28630
                                           in
                                        FStar_Syntax_Syntax.mk uu____28629
                                         in
                                      uu____28622
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
                                     let uu____28710 =
                                       let uu____28717 =
                                         let uu____28718 =
                                           let uu____28735 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28738 =
                                             let uu____28749 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28758 =
                                               let uu____28769 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28769; wpc1_2]  in
                                             uu____28749 :: uu____28758  in
                                           (uu____28735, uu____28738)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28718
                                          in
                                       FStar_Syntax_Syntax.mk uu____28717  in
                                     uu____28710 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28823 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28823
                              then
                                let uu____28828 =
                                  let uu____28830 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28830
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28828
                              else ());
                             (let uu____28834 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28834 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28843 =
                                      let uu____28846 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _28849  ->
                                           FStar_Pervasives_Native.Some
                                             _28849) uu____28846
                                       in
                                    solve_prob orig uu____28843 [] wl1  in
                                  let uu____28850 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28850))))
           in
        let uu____28851 = FStar_Util.physical_equality c1 c2  in
        if uu____28851
        then
          let uu____28854 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28854
        else
          ((let uu____28858 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28858
            then
              let uu____28863 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28865 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28863
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28865
            else ());
           (let uu____28870 =
              let uu____28879 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28882 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28879, uu____28882)  in
            match uu____28870 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28900),FStar_Syntax_Syntax.Total
                    (t2,uu____28902)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____28919 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28919 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28921,FStar_Syntax_Syntax.Total uu____28922) ->
                     let uu____28939 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____28939 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28943),FStar_Syntax_Syntax.Total
                    (t2,uu____28945)) ->
                     let uu____28962 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28962 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28965),FStar_Syntax_Syntax.GTotal
                    (t2,uu____28967)) ->
                     let uu____28984 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28984 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28987),FStar_Syntax_Syntax.GTotal
                    (t2,uu____28989)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29006 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29006 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29009),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29011)) ->
                     let uu____29028 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29028 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29031,FStar_Syntax_Syntax.Comp uu____29032) ->
                     let uu____29041 =
                       let uu___3790_29044 = problem  in
                       let uu____29047 =
                         let uu____29048 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29048
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3790_29044.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29047;
                         FStar_TypeChecker_Common.relation =
                           (uu___3790_29044.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3790_29044.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3790_29044.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3790_29044.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3790_29044.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3790_29044.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3790_29044.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3790_29044.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29041 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29049,FStar_Syntax_Syntax.Comp uu____29050) ->
                     let uu____29059 =
                       let uu___3790_29062 = problem  in
                       let uu____29065 =
                         let uu____29066 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29066
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3790_29062.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29065;
                         FStar_TypeChecker_Common.relation =
                           (uu___3790_29062.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3790_29062.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3790_29062.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3790_29062.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3790_29062.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3790_29062.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3790_29062.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3790_29062.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29059 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29067,FStar_Syntax_Syntax.GTotal uu____29068) ->
                     let uu____29077 =
                       let uu___3802_29080 = problem  in
                       let uu____29083 =
                         let uu____29084 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29084
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3802_29080.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3802_29080.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3802_29080.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29083;
                         FStar_TypeChecker_Common.element =
                           (uu___3802_29080.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3802_29080.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3802_29080.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3802_29080.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3802_29080.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3802_29080.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29077 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29085,FStar_Syntax_Syntax.Total uu____29086) ->
                     let uu____29095 =
                       let uu___3802_29098 = problem  in
                       let uu____29101 =
                         let uu____29102 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29102
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3802_29098.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3802_29098.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3802_29098.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29101;
                         FStar_TypeChecker_Common.element =
                           (uu___3802_29098.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3802_29098.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3802_29098.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3802_29098.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3802_29098.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3802_29098.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29095 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29103,FStar_Syntax_Syntax.Comp uu____29104) ->
                     let uu____29105 =
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
                     if uu____29105
                     then
                       let uu____29108 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29108 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29115 =
                            let uu____29120 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29120
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29129 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29130 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29129, uu____29130))
                             in
                          match uu____29115 with
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
                           (let uu____29138 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29138
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29146 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29146 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29149 =
                                  FStar_Thunk.mk
                                    (fun uu____29154  ->
                                       let uu____29155 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29157 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29155 uu____29157)
                                   in
                                giveup env uu____29149 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29168 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29168 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29218 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29218 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29243 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29274  ->
                match uu____29274 with
                | (u1,u2) ->
                    let uu____29282 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29284 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29282 uu____29284))
         in
      FStar_All.pipe_right uu____29243 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29321,[])) when
          let uu____29348 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29348 -> "{}"
      | uu____29351 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29378 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29378
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29390 =
              FStar_List.map
                (fun uu____29403  ->
                   match uu____29403 with
                   | (uu____29410,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29390 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29421 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29421 imps
  
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
                  let uu____29478 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29478
                  then
                    let uu____29486 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29488 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29486
                      (rel_to_string rel) uu____29488
                  else "TOP"  in
                let uu____29494 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29494 with
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
              let uu____29554 =
                let uu____29557 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29560  -> FStar_Pervasives_Native.Some _29560)
                  uu____29557
                 in
              FStar_Syntax_Syntax.new_bv uu____29554 t1  in
            let uu____29561 =
              let uu____29566 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29566
               in
            match uu____29561 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29624 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29624
         then
           let uu____29629 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29629
         else ());
        (let uu____29636 =
           FStar_Util.record_time (fun uu____29643  -> solve env probs)  in
         match uu____29636 with
         | (sol,ms) ->
             ((let uu____29655 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29655
               then
                 let uu____29660 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29660
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29673 =
                     FStar_Util.record_time
                       (fun uu____29680  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29673 with
                    | ((),ms1) ->
                        ((let uu____29691 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29691
                          then
                            let uu____29696 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29696
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29708 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29708
                     then
                       let uu____29715 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29715
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
          ((let uu____29741 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29741
            then
              let uu____29746 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29746
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29754 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29754
             then
               let uu____29759 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29759
             else ());
            (let f2 =
               let uu____29765 =
                 let uu____29766 = FStar_Syntax_Util.unmeta f1  in
                 uu____29766.FStar_Syntax_Syntax.n  in
               match uu____29765 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29770 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3919_29771 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3919_29771.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3919_29771.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3919_29771.FStar_TypeChecker_Common.implicits)
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
            let uu____29814 =
              let uu____29815 =
                let uu____29816 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29817  ->
                       FStar_TypeChecker_Common.NonTrivial _29817)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29816;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29815  in
            FStar_All.pipe_left
              (fun _29824  -> FStar_Pervasives_Native.Some _29824)
              uu____29814
  
let with_guard_no_simp :
  'Auu____29834 .
    'Auu____29834 ->
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
            let uu____29874 =
              let uu____29875 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29876  -> FStar_TypeChecker_Common.NonTrivial _29876)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29875;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____29874
  
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
          (let uu____29909 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____29909
           then
             let uu____29914 = FStar_Syntax_Print.term_to_string t1  in
             let uu____29916 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____29914
               uu____29916
           else ());
          (let uu____29921 =
             let uu____29926 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____29926
              in
           match uu____29921 with
           | (prob,wl) ->
               let g =
                 let uu____29934 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____29942  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____29934  in
               ((let uu____29960 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____29960
                 then
                   let uu____29965 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____29965
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
        let uu____29986 = try_teq true env t1 t2  in
        match uu____29986 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____29991 = FStar_TypeChecker_Env.get_range env  in
              let uu____29992 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____29991 uu____29992);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30000 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30000
              then
                let uu____30005 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30007 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30009 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30005
                  uu____30007 uu____30009
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
        (let uu____30033 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30033
         then
           let uu____30038 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30040 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30038
             uu____30040
         else ());
        (let uu____30045 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30045 with
         | (prob,x,wl) ->
             let g =
               let uu____30060 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30069  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30060  in
             ((let uu____30087 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30087
               then
                 let uu____30092 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30092
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30100 =
                     let uu____30101 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30101 g1  in
                   FStar_Pervasives_Native.Some uu____30100)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30123 = FStar_TypeChecker_Env.get_range env  in
          let uu____30124 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30123 uu____30124
  
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
        (let uu____30153 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30153
         then
           let uu____30158 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30160 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30158 uu____30160
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30171 =
           let uu____30178 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30178 "sub_comp"
            in
         match uu____30171 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30191 =
                 FStar_Util.record_time
                   (fun uu____30203  ->
                      let uu____30204 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30213  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30204)
                  in
               match uu____30191 with
               | (r,ms) ->
                   ((let uu____30241 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30241
                     then
                       let uu____30246 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30248 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30250 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30246 uu____30248
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30250
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
      fun uu____30288  ->
        match uu____30288 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30331 =
                 let uu____30337 =
                   let uu____30339 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30341 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30339 uu____30341
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30337)  in
               let uu____30345 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30331 uu____30345)
               in
            let equiv1 v1 v' =
              let uu____30358 =
                let uu____30363 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30364 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30363, uu____30364)  in
              match uu____30358 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30384 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____30415 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30415 with
                      | FStar_Syntax_Syntax.U_unif uu____30422 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30451  ->
                                    match uu____30451 with
                                    | (u,v') ->
                                        let uu____30460 = equiv1 v1 v'  in
                                        if uu____30460
                                        then
                                          let uu____30465 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30465 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____30486 -> []))
               in
            let uu____30491 =
              let wl =
                let uu___4030_30495 = empty_worklist env  in
                {
                  attempting = (uu___4030_30495.attempting);
                  wl_deferred = (uu___4030_30495.wl_deferred);
                  ctr = (uu___4030_30495.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4030_30495.smt_ok);
                  umax_heuristic_ok = (uu___4030_30495.umax_heuristic_ok);
                  tcenv = (uu___4030_30495.tcenv);
                  wl_implicits = (uu___4030_30495.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30514  ->
                      match uu____30514 with
                      | (lb,v1) ->
                          let uu____30521 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30521 with
                           | USolved wl1 -> ()
                           | uu____30524 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30535 =
              match uu____30535 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30547) -> true
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
                      uu____30571,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30573,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30584) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30592,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30601 -> false)
               in
            let uu____30607 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30624  ->
                      match uu____30624 with
                      | (u,v1) ->
                          let uu____30632 = check_ineq (u, v1)  in
                          if uu____30632
                          then true
                          else
                            ((let uu____30640 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30640
                              then
                                let uu____30645 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30647 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30645
                                  uu____30647
                              else ());
                             false)))
               in
            if uu____30607
            then ()
            else
              ((let uu____30657 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30657
                then
                  ((let uu____30663 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30663);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30675 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30675))
                else ());
               (let uu____30688 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30688))
  
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
        let fail1 uu____30761 =
          match uu____30761 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4107_30784 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4107_30784.attempting);
            wl_deferred = (uu___4107_30784.wl_deferred);
            ctr = (uu___4107_30784.ctr);
            defer_ok;
            smt_ok = (uu___4107_30784.smt_ok);
            umax_heuristic_ok = (uu___4107_30784.umax_heuristic_ok);
            tcenv = (uu___4107_30784.tcenv);
            wl_implicits = (uu___4107_30784.wl_implicits)
          }  in
        (let uu____30787 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30787
         then
           let uu____30792 = FStar_Util.string_of_bool defer_ok  in
           let uu____30794 = wl_to_string wl  in
           let uu____30796 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30792 uu____30794 uu____30796
         else ());
        (let g1 =
           let uu____30802 = solve_and_commit env wl fail1  in
           match uu____30802 with
           | FStar_Pervasives_Native.Some
               (uu____30809::uu____30810,uu____30811) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4122_30840 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4122_30840.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4122_30840.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30841 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4127_30850 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4127_30850.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4127_30850.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4127_30850.FStar_TypeChecker_Common.implicits)
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
          (let uu____30926 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook")
              in
           if uu____30926
           then
             let uu____30931 = guard_to_string env g  in
             let uu____30933 = FStar_Util.stack_dump ()  in
             FStar_Util.print2
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\nbacktrace=%s\n"
               uu____30931 uu____30933
           else ());
          (let g1 = solve_deferred_constraints env g  in
           let ret_g =
             let uu___4141_30940 = g1  in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred =
                 (uu___4141_30940.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4141_30940.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4141_30940.FStar_TypeChecker_Common.implicits)
             }  in
           let uu____30941 =
             let uu____30943 = FStar_TypeChecker_Env.should_verify env  in
             Prims.op_Negation uu____30943  in
           if uu____30941
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial  ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug1
                   then
                     (let uu____30955 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____30956 =
                        let uu____30958 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____30958
                         in
                      FStar_Errors.diag uu____30955 uu____30956)
                   else ();
                   (let vc1 =
                      let uu____30964 =
                        let uu____30968 =
                          let uu____30970 =
                            FStar_TypeChecker_Env.current_module env  in
                          FStar_Ident.string_of_lid uu____30970  in
                        FStar_Pervasives_Native.Some uu____30968  in
                      FStar_Profiling.profile
                        (fun uu____30973  ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____30964 "FStar.TypeChecker.Rel.vc_normalization"
                       in
                    if debug1
                    then
                      (let uu____30977 = FStar_TypeChecker_Env.get_range env
                          in
                       let uu____30978 =
                         let uu____30980 =
                           FStar_Syntax_Print.term_to_string vc1  in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____30980
                          in
                       FStar_Errors.diag uu____30977 uu____30978)
                    else ();
                    (let uu____30986 = FStar_TypeChecker_Env.get_range env
                        in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____30986 "discharge_guard'" env vc1);
                    (let uu____30988 =
                       FStar_TypeChecker_Common.check_trivial vc1  in
                     match uu____30988 with
                     | FStar_TypeChecker_Common.Trivial  ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug1
                            then
                              (let uu____30997 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____30998 =
                                 let uu____31000 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31000
                                  in
                               FStar_Errors.diag uu____30997 uu____30998)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug1
                            then
                              (let uu____31010 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31011 =
                                 let uu____31013 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31013
                                  in
                               FStar_Errors.diag uu____31010 uu____31011)
                            else ();
                            (let vcs =
                               let uu____31027 = FStar_Options.use_tactics ()
                                  in
                               if uu____31027
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31049  ->
                                      (let uu____31051 =
                                         FStar_Options.set_options
                                           "--no_tactics"
                                          in
                                       FStar_All.pipe_left (fun a1  -> ())
                                         uu____31051);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2
                                          in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____31095  ->
                                               match uu____31095 with
                                               | (env1,goal,opts) ->
                                                   let uu____31111 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal
                                                      in
                                                   (env1, uu____31111, opts)))))
                               else
                                 (let uu____31115 =
                                    let uu____31122 = FStar_Options.peek ()
                                       in
                                    (env, vc2, uu____31122)  in
                                  [uu____31115])
                                in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____31155  ->
                                     match uu____31155 with
                                     | (env1,goal,opts) ->
                                         let uu____31165 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal
                                            in
                                         (match uu____31165 with
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
                                                 (let uu____31176 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31177 =
                                                    let uu____31179 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    let uu____31181 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1
                                                       in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____31179 uu____31181
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31176 uu____31177)
                                               else ();
                                               if debug1
                                               then
                                                 (let uu____31188 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31189 =
                                                    let uu____31191 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____31191
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31188 uu____31189)
                                               else ();
                                               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                 use_env_range_msg env1 goal1;
                                               FStar_Options.pop ())))));
                            FStar_Pervasives_Native.Some ret_g))))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31209 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31209 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31218 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31218
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31232 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31232 with
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
        let uu____31262 = try_teq false env t1 t2  in
        match uu____31262 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
  
let (teq_maybe_defer :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let should_defer =
          let uu____31292 =
            FStar_TypeChecker_Env.lookup_attr env
              FStar_Parser_Const.resolve_implicits_attr_string
             in
          match uu____31292 with | [] -> false | uu____31297 -> true  in
        if should_defer
        then
          let uu____31302 =
            let uu____31307 = FStar_TypeChecker_Env.get_range env  in
            new_t_problem (empty_worklist env) env t1
              FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
              uu____31307
             in
          match uu____31302 with
          | (prob,wl) ->
              let wl1 =
                let uu____31311 =
                  FStar_Thunk.mkv
                    "deferring for user-provided resolve_implicits hook"
                   in
                defer uu____31311 prob wl  in
              let g =
                let uu____31317 =
                  solve_and_commit env wl1
                    (fun uu____31325  -> FStar_Pervasives_Native.None)
                   in
                FStar_All.pipe_left (with_guard env prob) uu____31317  in
              let g1 = FStar_Option.get g  in
              ((let uu____31344 =
                  FStar_TypeChecker_Env.debug env
                    (FStar_Options.Other "ResolveImplicitsHook")
                   in
                if uu____31344
                then
                  let uu____31348 =
                    let uu____31350 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Range.string_of_range uu____31350  in
                  let uu____31351 = guard_to_string env g1  in
                  FStar_Util.print2 "(%s): Deferred unification: %s\n"
                    uu____31348 uu____31351
                else ());
               g1)
        else teq env t1 t2
  
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
            let uu____31390 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31390 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31397 ->
                     let uu____31398 =
                       let uu____31399 = FStar_Syntax_Subst.compress r  in
                       uu____31399.FStar_Syntax_Syntax.n  in
                     (match uu____31398 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31404) ->
                          unresolved ctx_u'
                      | uu____31421 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31445 = acc  in
            match uu____31445 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____31464 = hd1  in
                     (match uu____31464 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____31475 = unresolved ctx_u  in
                             if uu____31475
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   (env_dyn,tau)) ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31487 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31487
                                     then
                                       let uu____31491 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31491
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31500 = teq_nosmt env1 t tm
                                          in
                                       match uu____31500 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4271_31510 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4271_31510.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4271_31510.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4271_31510.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4271_31510.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4271_31510.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4271_31510.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4271_31510.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4274_31512 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4274_31512.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4274_31512.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4274_31512.FStar_TypeChecker_Common.imp_range)
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
                                    let uu___4278_31523 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4278_31523.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4278_31523.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4278_31523.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4278_31523.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4278_31523.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4278_31523.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4278_31523.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4278_31523.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4278_31523.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4278_31523.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4278_31523.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4278_31523.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4278_31523.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4278_31523.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4278_31523.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4278_31523.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4278_31523.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4278_31523.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4278_31523.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4278_31523.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4278_31523.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4278_31523.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4278_31523.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4278_31523.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4278_31523.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4278_31523.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4278_31523.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4278_31523.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4278_31523.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4278_31523.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4278_31523.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4278_31523.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4278_31523.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4278_31523.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4278_31523.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4278_31523.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4278_31523.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4278_31523.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4278_31523.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4278_31523.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4278_31523.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4278_31523.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4278_31523.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4278_31523.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4278_31523.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4278_31523.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4283_31528 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4283_31528.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4283_31528.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4283_31528.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4283_31528.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4283_31528.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4283_31528.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4283_31528.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4283_31528.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4283_31528.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4283_31528.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4283_31528.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4283_31528.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4283_31528.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4283_31528.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4283_31528.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4283_31528.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4283_31528.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4283_31528.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4283_31528.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4283_31528.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4283_31528.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4283_31528.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4283_31528.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4283_31528.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4283_31528.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4283_31528.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4283_31528.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4283_31528.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4283_31528.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4283_31528.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4283_31528.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4283_31528.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4283_31528.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4283_31528.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4283_31528.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4283_31528.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4283_31528.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4283_31528.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4283_31528.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4283_31528.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4283_31528.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4283_31528.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4283_31528.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4283_31528.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4283_31528.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4283_31528.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31533 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31533
                                   then
                                     let uu____31538 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31540 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31542 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31544 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31538 uu____31540 uu____31542
                                       reason uu____31544
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4289_31551  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31558 =
                                             let uu____31568 =
                                               let uu____31576 =
                                                 let uu____31578 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31580 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31582 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31578 uu____31580
                                                   uu____31582
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31576, r)
                                                in
                                             [uu____31568]  in
                                           FStar_Errors.add_errors
                                             uu____31558);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31601 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31612  ->
                                               let uu____31613 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31615 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31617 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31613 uu____31615
                                                 reason uu____31617)) env2 g1
                                         true
                                        in
                                     match uu____31601 with
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
          let uu___4301_31625 = g  in
          let uu____31626 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4301_31625.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4301_31625.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4301_31625.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31626
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      (let uu____31641 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____31641
       then
         let uu____31646 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____31646
       else ());
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
      (let uu____31677 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____31677
       then
         let uu____31682 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____31682
       else ());
      (let g1 =
         let uu____31688 = solve_deferred_constraints env g  in
         FStar_All.pipe_right uu____31688 (resolve_implicits env)  in
       match g1.FStar_TypeChecker_Common.implicits with
       | [] ->
           let uu____31689 = discharge_guard env g1  in
           FStar_All.pipe_left (fun a2  -> ()) uu____31689
       | imp::uu____31691 ->
           let uu____31694 =
             FStar_TypeChecker_Env.lookup_attr env
               FStar_Parser_Const.resolve_implicits_attr_string
              in
           (match uu____31694 with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  (uu____31697,lid::[]);
                FStar_Syntax_Syntax.sigrng = uu____31699;
                FStar_Syntax_Syntax.sigquals = uu____31700;
                FStar_Syntax_Syntax.sigmeta = uu____31701;
                FStar_Syntax_Syntax.sigattrs = uu____31702;
                FStar_Syntax_Syntax.sigopts = uu____31703;_}::uu____31704 ->
                let qn = FStar_TypeChecker_Env.lookup_qname env lid  in
                let fv =
                  FStar_Syntax_Syntax.lid_as_fv lid
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero) FStar_Pervasives_Native.None
                   in
                let dd =
                  let uu____31719 =
                    FStar_TypeChecker_Env.delta_depth_of_qninfo fv qn  in
                  match uu____31719 with
                  | FStar_Pervasives_Native.Some dd -> dd
                  | FStar_Pervasives_Native.None  -> failwith "Expected a dd"
                   in
                let term =
                  let uu____31725 =
                    FStar_Syntax_Syntax.lid_as_fv lid dd
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.fv_to_tm uu____31725  in
                (env.FStar_TypeChecker_Env.try_solve_implicits_hook env term
                   g1.FStar_TypeChecker_Common.implicits;
                 (let uu____31727 = discharge_guard env g1  in
                  FStar_All.pipe_left (fun a3  -> ()) uu____31727))
            | uu____31728 ->
                let uu____31731 =
                  let uu____31737 =
                    let uu____31739 =
                      FStar_Syntax_Print.uvar_to_string
                        (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                       in
                    let uu____31741 =
                      FStar_TypeChecker_Normalize.term_to_string env
                        (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                       in
                    FStar_Util.format3
                      "Failed to resolve implicit argument %s of type %s introduced for %s"
                      uu____31739 uu____31741
                      imp.FStar_TypeChecker_Common.imp_reason
                     in
                  (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                    uu____31737)
                   in
                FStar_Errors.raise_error uu____31731
                  imp.FStar_TypeChecker_Common.imp_range))
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31761 = teq env t1 t2  in
        force_trivial_guard env uu____31761
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31780 = teq_nosmt env t1 t2  in
        match uu____31780 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4352_31799 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4352_31799.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4352_31799.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4352_31799.FStar_TypeChecker_Common.implicits)
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
        (let uu____31835 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31835
         then
           let uu____31840 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31842 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31840
             uu____31842
         else ());
        (let uu____31847 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31847 with
         | (prob,x,wl) ->
             let g =
               let uu____31866 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31875  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31866  in
             ((let uu____31893 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31893
               then
                 let uu____31898 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31900 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31902 =
                   let uu____31904 = FStar_Util.must g  in
                   guard_to_string env uu____31904  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31898 uu____31900 uu____31902
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
        let uu____31941 = check_subtyping env t1 t2  in
        match uu____31941 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31960 =
              let uu____31961 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31961 g  in
            FStar_Pervasives_Native.Some uu____31960
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31980 = check_subtyping env t1 t2  in
        match uu____31980 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31999 =
              let uu____32000 =
                let uu____32001 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____32001]  in
              FStar_TypeChecker_Env.close_guard env uu____32000 g  in
            FStar_Pervasives_Native.Some uu____31999
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32039 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32039
         then
           let uu____32044 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32046 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32044
             uu____32046
         else ());
        (let uu____32051 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32051 with
         | (prob,x,wl) ->
             let g =
               let uu____32066 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32075  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32066  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32096 =
                      let uu____32097 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32097]  in
                    FStar_TypeChecker_Env.close_guard env uu____32096 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32138 = subtype_nosmt env t1 t2  in
        match uu____32138 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  