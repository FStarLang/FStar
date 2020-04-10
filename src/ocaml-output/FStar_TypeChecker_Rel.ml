open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type lstring = Prims.string FStar_Thunk.t
let (mklstr : (unit -> Prims.string) -> Prims.string FStar_Thunk.thunk) =
  fun f  ->
    let uf = FStar_Syntax_Unionfind.get ()  in
    FStar_Thunk.mk
      (fun uu____40  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         FStar_Syntax_Unionfind.set uf;
         (let r = f ()  in FStar_Syntax_Unionfind.rollback tx; r))
  
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____78 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____113 -> false
  
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
                    let uu____570 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____570;
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
                   (let uu____602 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace")
                       in
                    if uu____602
                    then
                      let uu____606 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                         in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____606
                    else ());
                   (ctx_uvar, t,
                     ((let uu___80_612 = wl  in
                       {
                         attempting = (uu___80_612.attempting);
                         wl_deferred = (uu___80_612.wl_deferred);
                         ctr = (uu___80_612.ctr);
                         defer_ok = (uu___80_612.defer_ok);
                         smt_ok = (uu___80_612.smt_ok);
                         umax_heuristic_ok = (uu___80_612.umax_heuristic_ok);
                         tcenv = (uu___80_612.tcenv);
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
            let uu___86_645 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___86_645.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___86_645.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___86_645.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___86_645.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___86_645.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___86_645.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___86_645.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___86_645.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___86_645.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___86_645.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___86_645.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___86_645.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___86_645.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___86_645.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___86_645.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___86_645.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___86_645.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___86_645.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___86_645.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___86_645.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___86_645.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___86_645.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___86_645.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___86_645.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___86_645.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___86_645.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___86_645.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___86_645.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___86_645.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___86_645.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___86_645.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___86_645.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___86_645.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___86_645.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___86_645.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___86_645.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___86_645.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___86_645.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___86_645.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___86_645.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___86_645.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___86_645.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___86_645.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___86_645.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___86_645.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___86_645.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____647 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____647 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____734 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____769 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____799 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____810 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____821 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_839  ->
    match uu___0_839 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____851 = FStar_Syntax_Util.head_and_args t  in
    match uu____851 with
    | (head,args) ->
        (match head.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____914 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____916 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____931 =
                     let uu____933 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____933  in
                   FStar_Util.format1 "@<%s>" uu____931
                in
             let uu____937 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____914 uu____916 uu____937
         | uu____940 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_952  ->
      match uu___1_952 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____957 =
            let uu____961 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____963 =
              let uu____967 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____969 =
                let uu____973 =
                  let uu____977 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____977]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____973
                 in
              uu____967 :: uu____969  in
            uu____961 :: uu____963  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____957
      | FStar_TypeChecker_Common.CProb p ->
          let uu____988 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____990 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____992 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____988 uu____990
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____992
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_1006  ->
      match uu___2_1006 with
      | UNIV (u,t) ->
          let x =
            let uu____1012 = FStar_Options.hide_uvar_nums ()  in
            if uu____1012
            then "?"
            else
              (let uu____1019 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1019 FStar_Util.string_of_int)
             in
          let uu____1023 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s <- %s" x uu____1023
      | TERM (u,t) ->
          let x =
            let uu____1030 = FStar_Options.hide_uvar_nums ()  in
            if uu____1030
            then "?"
            else
              (let uu____1037 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1037 FStar_Util.string_of_int)
             in
          let uu____1041 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s <- %s" x uu____1041
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  -> FStar_Common.string_of_list (uvi_to_string env) uvis
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1071 =
      let uu____1075 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1075
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1071 (FStar_String.concat ", ")
  
let args_to_string :
  'uuuuuu1094 .
    (FStar_Syntax_Syntax.term * 'uuuuuu1094) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1113 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1134  ->
              match uu____1134 with
              | (x,uu____1141) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1113 (FStar_String.concat " ")
  
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
        (let uu____1181 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1181
         then
           let uu____1186 = FStar_Thunk.force reason  in
           let uu____1189 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1186 uu____1189
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1212 = mklstr (fun uu____1215  -> reason)  in
        giveup env uu____1212 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1221  ->
    match uu___3_1221 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'uuuuuu1227 .
    'uuuuuu1227 FStar_TypeChecker_Common.problem ->
      'uuuuuu1227 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___150_1239 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___150_1239.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___150_1239.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___150_1239.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___150_1239.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___150_1239.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___150_1239.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___150_1239.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'uuuuuu1247 .
    'uuuuuu1247 FStar_TypeChecker_Common.problem ->
      'uuuuuu1247 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1267  ->
    match uu___4_1267 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1273  -> FStar_TypeChecker_Common.TProb uu____1273)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1279  -> FStar_TypeChecker_Common.CProb uu____1279)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1285  ->
    match uu___5_1285 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___162_1291 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___162_1291.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___162_1291.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___162_1291.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___162_1291.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___162_1291.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___162_1291.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___162_1291.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___162_1291.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___162_1291.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___166_1299 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___166_1299.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___166_1299.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___166_1299.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___166_1299.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___166_1299.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___166_1299.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___166_1299.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___166_1299.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___166_1299.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1312  ->
      match uu___6_1312 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1319  ->
    match uu___7_1319 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1332  ->
    match uu___8_1332 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1347  ->
    match uu___9_1347 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1362  ->
    match uu___10_1362 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1376  ->
    match uu___11_1376 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1390  ->
    match uu___12_1390 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1402  ->
    match uu___13_1402 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'uuuuuu1418 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu1418) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1448 =
          let uu____1450 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1450  in
        if uu____1448
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1487)::bs ->
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
          let uu____1534 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1558 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1558]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1534
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1586 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1610 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1610]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1586
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1657 =
          let uu____1659 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1659  in
        if uu____1657
        then ()
        else
          (let uu____1664 =
             let uu____1667 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1667
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1664 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1716 =
          let uu____1718 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1718  in
        if uu____1716
        then ()
        else
          (let uu____1723 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1723)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1743 =
        let uu____1745 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1745  in
      if uu____1743
      then ()
      else
        (let msgf m =
           let uu____1759 =
             let uu____1761 =
               let uu____1763 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____1763 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____1761  in
           Prims.op_Hat msg uu____1759  in
         (let uu____1768 = msgf "scope"  in
          let uu____1771 = p_scope prob  in
          def_scope_wf uu____1768 (p_loc prob) uu____1771);
         (let uu____1783 = msgf "guard"  in
          def_check_scoped uu____1783 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1790 = msgf "lhs"  in
                def_check_scoped uu____1790 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1793 = msgf "rhs"  in
                def_check_scoped uu____1793 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1800 = msgf "lhs"  in
                def_check_scoped_comp uu____1800 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1803 = msgf "rhs"  in
                def_check_scoped_comp uu____1803 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___259_1824 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___259_1824.wl_deferred);
          ctr = (uu___259_1824.ctr);
          defer_ok = (uu___259_1824.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___259_1824.umax_heuristic_ok);
          tcenv = (uu___259_1824.tcenv);
          wl_implicits = (uu___259_1824.wl_implicits)
        }
  
let wl_of_guard :
  'uuuuuu1832 .
    FStar_TypeChecker_Env.env ->
      ('uuuuuu1832 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___263_1855 = empty_worklist env  in
      let uu____1856 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1856;
        wl_deferred = (uu___263_1855.wl_deferred);
        ctr = (uu___263_1855.ctr);
        defer_ok = (uu___263_1855.defer_ok);
        smt_ok = (uu___263_1855.smt_ok);
        umax_heuristic_ok = (uu___263_1855.umax_heuristic_ok);
        tcenv = (uu___263_1855.tcenv);
        wl_implicits = (uu___263_1855.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___268_1877 = wl  in
        {
          attempting = (uu___268_1877.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___268_1877.ctr);
          defer_ok = (uu___268_1877.defer_ok);
          smt_ok = (uu___268_1877.smt_ok);
          umax_heuristic_ok = (uu___268_1877.umax_heuristic_ok);
          tcenv = (uu___268_1877.tcenv);
          wl_implicits = (uu___268_1877.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____1904 = FStar_Thunk.mkv reason  in defer uu____1904 prob wl
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___276_1923 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___276_1923.wl_deferred);
         ctr = (uu___276_1923.ctr);
         defer_ok = (uu___276_1923.defer_ok);
         smt_ok = (uu___276_1923.smt_ok);
         umax_heuristic_ok = (uu___276_1923.umax_heuristic_ok);
         tcenv = (uu___276_1923.tcenv);
         wl_implicits = (uu___276_1923.wl_implicits)
       })
  
let mk_eq2 :
  'uuuuuu1937 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu1937 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____1971 = FStar_Syntax_Util.type_u ()  in
            match uu____1971 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____1983 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____1983 with
                 | (uu____2001,tt,wl1) ->
                     let uu____2004 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____2004, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2010  ->
    match uu___14_2010 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun uu____2016  -> FStar_TypeChecker_Common.TProb uu____2016)
          (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun uu____2022  -> FStar_TypeChecker_Common.CProb uu____2022)
          (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2030 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2030 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2050  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'uuuuuu2092 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'uuuuuu2092 ->
            FStar_TypeChecker_Common.rel ->
              'uuuuuu2092 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('uuuuuu2092 FStar_TypeChecker_Common.problem * worklist)
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
                        let uu____2179 =
                          let uu____2188 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2188]  in
                        FStar_List.append scope uu____2179
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2231 =
                      let uu____2234 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2234  in
                    FStar_List.append uu____2231
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2253 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2253 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2279 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2279;
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
                  (let uu____2353 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2353 with
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
                  (let uu____2441 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2441 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'uuuuuu2479 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu2479 ->
          FStar_TypeChecker_Common.rel ->
            'uuuuuu2479 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('uuuuuu2479 FStar_TypeChecker_Common.problem * worklist)
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
                          let uu____2547 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2547]  in
                        let uu____2566 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2566
                     in
                  let uu____2569 =
                    let uu____2576 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___359_2587 = wl  in
                       {
                         attempting = (uu___359_2587.attempting);
                         wl_deferred = (uu___359_2587.wl_deferred);
                         ctr = (uu___359_2587.ctr);
                         defer_ok = (uu___359_2587.defer_ok);
                         smt_ok = (uu___359_2587.smt_ok);
                         umax_heuristic_ok =
                           (uu___359_2587.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___359_2587.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2576
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2569 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2605 =
                              let uu____2610 =
                                let uu____2611 =
                                  let uu____2620 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2620
                                   in
                                [uu____2611]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2610  in
                            uu____2605 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2648 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2648;
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
                let uu____2696 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2696;
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
  'uuuuuu2711 .
    worklist ->
      'uuuuuu2711 FStar_TypeChecker_Common.problem ->
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
              let uu____2744 =
                let uu____2747 =
                  let uu____2748 =
                    let uu____2755 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2755)  in
                  FStar_Syntax_Syntax.NT uu____2748  in
                [uu____2747]  in
              FStar_Syntax_Subst.subst uu____2744 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2777 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2777
        then
          let uu____2785 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2788 = prob_to_string env d  in
          let uu____2790 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____2797 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2785 uu____2788 uu____2790 uu____2797
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2809 -> failwith "impossible"  in
           let uu____2812 =
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
           match uu____2812 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2855  ->
            match uu___15_2855 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2867 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2871 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2871 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2902  ->
           match uu___16_2902 with
           | UNIV uu____2905 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2912 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2912
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
        (fun uu___17_2940  ->
           match uu___17_2940 with
           | UNIV (u',t) ->
               let uu____2945 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2945
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2952 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2964 =
        let uu____2965 =
          let uu____2966 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2966
           in
        FStar_Syntax_Subst.compress uu____2965  in
      FStar_All.pipe_right uu____2964 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2978 =
        let uu____2979 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____2979  in
      FStar_All.pipe_right uu____2978 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2991 =
        let uu____2995 =
          let uu____2997 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____2997  in
        FStar_Pervasives_Native.Some uu____2995  in
      FStar_Profiling.profile (fun uu____3000  -> sn' env t) uu____2991
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
          let uu____3025 =
            let uu____3029 =
              let uu____3031 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3031  in
            FStar_Pervasives_Native.Some uu____3029  in
          FStar_Profiling.profile
            (fun uu____3034  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3025
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3042 = FStar_Syntax_Util.head_and_args t  in
    match uu____3042 with
    | (h,uu____3061) ->
        let uu____3086 =
          let uu____3087 = FStar_Syntax_Subst.compress h  in
          uu____3087.FStar_Syntax_Syntax.n  in
        (match uu____3086 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3092 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3105 =
        let uu____3109 =
          let uu____3111 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3111  in
        FStar_Pervasives_Native.Some uu____3109  in
      FStar_Profiling.profile
        (fun uu____3116  ->
           let uu____3117 = should_strongly_reduce t  in
           if uu____3117
           then
             let uu____3120 =
               let uu____3121 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3121  in
             FStar_All.pipe_right uu____3120 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3105 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'uuuuuu3132 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'uuuuuu3132) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu3132)
  =
  fun env  ->
    fun t  ->
      let uu____3155 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3155, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3207  ->
              match uu____3207 with
              | (x,imp) ->
                  let uu____3226 =
                    let uu___465_3227 = x  in
                    let uu____3228 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___465_3227.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___465_3227.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3228
                    }  in
                  (uu____3226, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3252 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3252
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3256 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3256
        | uu____3259 -> u2  in
      let uu____3260 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3260
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3277 =
          let uu____3281 =
            let uu____3283 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3283  in
          FStar_Pervasives_Native.Some uu____3281  in
        FStar_Profiling.profile
          (fun uu____3286  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3277 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
                (let uu____3408 = norm_refinement env t12  in
                 match uu____3408 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3423;
                     FStar_Syntax_Syntax.vars = uu____3424;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3448 =
                       let uu____3450 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3452 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3450 uu____3452
                        in
                     failwith uu____3448)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3468 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm uu____3468
          | FStar_Syntax_Syntax.Tm_uinst uu____3469 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3506 =
                   let uu____3507 = FStar_Syntax_Subst.compress t1'  in
                   uu____3507.FStar_Syntax_Syntax.n  in
                 match uu____3506 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3522 -> aux true t1'
                 | uu____3530 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3545 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3576 =
                   let uu____3577 = FStar_Syntax_Subst.compress t1'  in
                   uu____3577.FStar_Syntax_Syntax.n  in
                 match uu____3576 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3592 -> aux true t1'
                 | uu____3600 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3615 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3662 =
                   let uu____3663 = FStar_Syntax_Subst.compress t1'  in
                   uu____3663.FStar_Syntax_Syntax.n  in
                 match uu____3662 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3678 -> aux true t1'
                 | uu____3686 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3701 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3716 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3731 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3746 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3761 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3790 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3823 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3844 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3871 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3899 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3936 ->
              let uu____3943 =
                let uu____3945 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3947 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3945 uu____3947
                 in
              failwith uu____3943
          | FStar_Syntax_Syntax.Tm_ascribed uu____3962 ->
              let uu____3989 =
                let uu____3991 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3993 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3991 uu____3993
                 in
              failwith uu____3989
          | FStar_Syntax_Syntax.Tm_delayed uu____4008 ->
              let uu____4023 =
                let uu____4025 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4027 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4025 uu____4027
                 in
              failwith uu____4023
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4042 =
                let uu____4044 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4046 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4044 uu____4046
                 in
              failwith uu____4042
           in
        let uu____4061 = whnf env t1  in aux false uu____4061
  
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
      let uu____4106 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4106 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4147 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4147, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta  ->
    fun env  ->
      fun t  ->
        let uu____4174 = base_and_refinement_maybe_delta delta env t  in
        match uu____4174 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4234  ->
    match uu____4234 with
    | (t_base,refopt) ->
        let uu____4265 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4265 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4307 =
      let uu____4311 =
        let uu____4314 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4339  ->
                  match uu____4339 with | (uu____4347,uu____4348,x) -> x))
           in
        FStar_List.append wl.attempting uu____4314  in
      FStar_List.map (wl_prob_to_string wl) uu____4311  in
    FStar_All.pipe_right uu____4307 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'uuuuuu4369 .
    ('uuuuuu4369 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4381  ->
    match uu____4381 with
    | (uu____4388,c,args) ->
        let uu____4391 = print_ctx_uvar c  in
        let uu____4393 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4391 uu____4393
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4403 = FStar_Syntax_Util.head_and_args t  in
    match uu____4403 with
    | (head,_args) ->
        let uu____4447 =
          let uu____4448 = FStar_Syntax_Subst.compress head  in
          uu____4448.FStar_Syntax_Syntax.n  in
        (match uu____4447 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4452 -> true
         | uu____4466 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4474 = FStar_Syntax_Util.head_and_args t  in
    match uu____4474 with
    | (head,_args) ->
        let uu____4517 =
          let uu____4518 = FStar_Syntax_Subst.compress head  in
          uu____4518.FStar_Syntax_Syntax.n  in
        (match uu____4517 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4522) -> u
         | uu____4539 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4564 = FStar_Syntax_Util.head_and_args t  in
      match uu____4564 with
      | (head,args) ->
          let uu____4611 =
            let uu____4612 = FStar_Syntax_Subst.compress head  in
            uu____4612.FStar_Syntax_Syntax.n  in
          (match uu____4611 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4620)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4653 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_4678  ->
                         match uu___18_4678 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4683 =
                               let uu____4684 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4684.FStar_Syntax_Syntax.n  in
                             (match uu____4683 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4689 -> false)
                         | uu____4691 -> true))
                  in
               (match uu____4653 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4716 =
                        FStar_List.collect
                          (fun uu___19_4728  ->
                             match uu___19_4728 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4732 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4732]
                             | uu____4733 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4716 FStar_List.rev  in
                    let uu____4756 =
                      let uu____4763 =
                        let uu____4772 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_4794  ->
                                  match uu___20_4794 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4798 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4798]
                                  | uu____4799 -> []))
                           in
                        FStar_All.pipe_right uu____4772 FStar_List.rev  in
                      let uu____4822 =
                        let uu____4825 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4825  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4763 uu____4822
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____4756 with
                     | (v,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4861  ->
                                match uu____4861 with
                                | (x,i) ->
                                    let uu____4880 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4880, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4911  ->
                                match uu____4911 with
                                | (a,i) ->
                                    let uu____4930 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4930, i)) args_sol
                            in
                         let all_args = FStar_List.append args_sol_s args  in
                         let t1 =
                           FStar_Syntax_Syntax.mk_Tm_app t_v all_args
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         (FStar_Syntax_Unionfind.change
                            uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                          ((t1, v, all_args), wl1))))
           | uu____4952 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4974 =
          let uu____4997 =
            let uu____4998 = FStar_Syntax_Subst.compress k  in
            uu____4998.FStar_Syntax_Syntax.n  in
          match uu____4997 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5080 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5080)
              else
                (let uu____5115 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5115 with
                 | (ys',t1,uu____5148) ->
                     let uu____5153 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5153))
          | uu____5192 ->
              let uu____5193 =
                let uu____5198 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5198)  in
              ((ys, t), uu____5193)
           in
        match uu____4974 with
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
                 let uu____5293 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5293 c  in
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
               (let uu____5371 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5371
                then
                  let uu____5376 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5378 = print_ctx_uvar uv  in
                  let uu____5380 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5376 uu____5378 uu____5380
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5389 =
                   let uu____5391 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5391  in
                 let uu____5394 =
                   let uu____5397 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5397
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5389 uu____5394 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail uu____5430 =
               let uu____5431 =
                 let uu____5433 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5435 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5433 uu____5435
                  in
               failwith uu____5431  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5501  ->
                       match uu____5501 with
                       | (a,i) ->
                           let uu____5522 =
                             let uu____5523 = FStar_Syntax_Subst.compress a
                                in
                             uu____5523.FStar_Syntax_Syntax.n  in
                           (match uu____5522 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5549 -> (fail (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5559 =
                 let uu____5561 = is_flex g  in Prims.op_Negation uu____5561
                  in
               if uu____5559
               then (if resolve_ok then wl else (fail (); wl))
               else
                 (let uu____5570 = destruct_flex_t g wl  in
                  match uu____5570 with
                  | ((uu____5575,uv1,args),wl1) ->
                      ((let uu____5580 = args_as_binders args  in
                        assign_solution uu____5580 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___718_5582 = wl1  in
              {
                attempting = (uu___718_5582.attempting);
                wl_deferred = (uu___718_5582.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___718_5582.defer_ok);
                smt_ok = (uu___718_5582.smt_ok);
                umax_heuristic_ok = (uu___718_5582.umax_heuristic_ok);
                tcenv = (uu___718_5582.tcenv);
                wl_implicits = (uu___718_5582.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5607 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5607
         then
           let uu____5612 = FStar_Util.string_of_int pid  in
           let uu____5614 = uvis_to_string wl.tcenv sol  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5612 uu____5614
         else ());
        commit sol;
        (let uu___726_5620 = wl  in
         {
           attempting = (uu___726_5620.attempting);
           wl_deferred = (uu___726_5620.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___726_5620.defer_ok);
           smt_ok = (uu___726_5620.smt_ok);
           umax_heuristic_ok = (uu___726_5620.umax_heuristic_ok);
           tcenv = (uu___726_5620.tcenv);
           wl_implicits = (uu___726_5620.wl_implicits)
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
          (let uu____5656 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____5656
           then
             let uu____5661 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____5665 = uvis_to_string wl.tcenv uvis  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5661 uu____5665
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
        let uu____5692 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5692 FStar_Util.set_elements  in
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
      let uu____5732 = occurs uk t  in
      match uu____5732 with
      | (uvars,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5771 =
                 let uu____5773 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5775 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5773 uu____5775
                  in
               FStar_Pervasives_Native.Some uu____5771)
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
          let uu____5886 = FStar_Syntax_Syntax.bv_eq b b'  in
          if uu____5886
          then
            let uu____5897 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5897 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5948 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6005  ->
             match uu____6005 with
             | (x,uu____6017) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6035 = FStar_List.last bs  in
      match uu____6035 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6059) ->
          let uu____6070 =
            FStar_Util.prefix_until
              (fun uu___21_6085  ->
                 match uu___21_6085 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6088 -> false) g
             in
          (match uu____6070 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6102,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6139 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6139 with
        | (pfx,uu____6149) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6161 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6161 with
             | (uu____6169,src',wl1) ->
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
                 | uu____6283 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6284 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6348  ->
                  fun uu____6349  ->
                    match (uu____6348, uu____6349) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6452 =
                          let uu____6454 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6454
                           in
                        if uu____6452
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6488 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6488
                           then
                             let uu____6505 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6505)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6284 with | (isect,uu____6555) -> FStar_List.rev isect
  
let binders_eq :
  'uuuuuu6591 'uuuuuu6592 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu6591) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6592) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6650  ->
              fun uu____6651  ->
                match (uu____6650, uu____6651) with
                | ((a,uu____6670),(b,uu____6672)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'uuuuuu6688 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6688) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6719  ->
           match uu____6719 with
           | (y,uu____6726) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'uuuuuu6736 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6736) Prims.list ->
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
                   let uu____6898 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6898
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6931 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6983 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7027 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7048 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7056  ->
    match uu___22_7056 with
    | MisMatch (d1,d2) ->
        let uu____7068 =
          let uu____7070 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7072 =
            let uu____7074 =
              let uu____7076 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7076 ")"  in
            Prims.op_Hat ") (" uu____7074  in
          Prims.op_Hat uu____7070 uu____7072  in
        Prims.op_Hat "MisMatch (" uu____7068
    | HeadMatch u ->
        let uu____7083 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7083
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7092  ->
    match uu___23_7092 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7109 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv  in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____7124 =
            (let uu____7130 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule
                in
             let uu____7132 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             uu____7130 = uu____7132) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
             in
          if uu____7124 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7141 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7141 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7152 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7176 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7186 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7205 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7205
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7206 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7207 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7208 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7221 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7235 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7259) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7265,uu____7266) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7308) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7333;
             FStar_Syntax_Syntax.index = uu____7334;
             FStar_Syntax_Syntax.sort = t2;_},uu____7336)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7344 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7345 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7346 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7361 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7368 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7388 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7388
  
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
           { FStar_Syntax_Syntax.blob = uu____7407;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7408;
             FStar_Syntax_Syntax.ltyp = uu____7409;
             FStar_Syntax_Syntax.rng = uu____7410;_},uu____7411)
            ->
            let uu____7422 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7422 t21
        | (uu____7423,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7424;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7425;
             FStar_Syntax_Syntax.ltyp = uu____7426;
             FStar_Syntax_Syntax.rng = uu____7427;_})
            ->
            let uu____7438 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7438
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7441 = FStar_Syntax_Syntax.bv_eq x y  in
            if uu____7441
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7452 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7452
            then FullMatch
            else
              (let uu____7457 =
                 let uu____7466 =
                   let uu____7469 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7469  in
                 let uu____7470 =
                   let uu____7473 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7473  in
                 (uu____7466, uu____7470)  in
               MisMatch uu____7457)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7479),FStar_Syntax_Syntax.Tm_uinst (g,uu____7481)) ->
            let uu____7490 = head_matches env f g  in
            FStar_All.pipe_right uu____7490 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7491) -> HeadMatch true
        | (uu____7493,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7497 = FStar_Const.eq_const c d  in
            if uu____7497
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7507),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7509)) ->
            let uu____7542 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7542
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7552),FStar_Syntax_Syntax.Tm_refine (y,uu____7554)) ->
            let uu____7563 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7563 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7565),uu____7566) ->
            let uu____7571 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7571 head_match
        | (uu____7572,FStar_Syntax_Syntax.Tm_refine (x,uu____7574)) ->
            let uu____7579 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7579 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7580,FStar_Syntax_Syntax.Tm_type
           uu____7581) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7583,FStar_Syntax_Syntax.Tm_arrow uu____7584) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head,uu____7615),FStar_Syntax_Syntax.Tm_app (head',uu____7617))
            ->
            let uu____7666 = head_matches env head head'  in
            FStar_All.pipe_right uu____7666 head_match
        | (FStar_Syntax_Syntax.Tm_app (head,uu____7668),uu____7669) ->
            let uu____7694 = head_matches env head t21  in
            FStar_All.pipe_right uu____7694 head_match
        | (uu____7695,FStar_Syntax_Syntax.Tm_app (head,uu____7697)) ->
            let uu____7722 = head_matches env t11 head  in
            FStar_All.pipe_right uu____7722 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7723,FStar_Syntax_Syntax.Tm_let
           uu____7724) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7752,FStar_Syntax_Syntax.Tm_match uu____7753) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7799,FStar_Syntax_Syntax.Tm_abs
           uu____7800) -> HeadMatch true
        | uu____7838 ->
            let uu____7843 =
              let uu____7852 = delta_depth_of_term env t11  in
              let uu____7855 = delta_depth_of_term env t21  in
              (uu____7852, uu____7855)  in
            MisMatch uu____7843
  
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
              let uu____7924 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7924  in
            (let uu____7926 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7926
             then
               let uu____7931 = FStar_Syntax_Print.term_to_string t  in
               let uu____7933 = FStar_Syntax_Print.term_to_string head  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7931 uu____7933
             else ());
            (let uu____7938 =
               let uu____7939 = FStar_Syntax_Util.un_uinst head  in
               uu____7939.FStar_Syntax_Syntax.n  in
             match uu____7938 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7945 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7945 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7959 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7959
                        then
                          let uu____7964 =
                            FStar_Syntax_Print.term_to_string head  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7964
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7969 ->
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
                      let uu____7987 =
                        let uu____7989 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7989 = FStar_Syntax_Util.Equal  in
                      if uu____7987
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7996 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7996
                          then
                            let uu____8001 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8003 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8001
                              uu____8003
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8008 -> FStar_Pervasives_Native.None)
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
            (let uu____8160 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8160
             then
               let uu____8165 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8167 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8169 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8165
                 uu____8167 uu____8169
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8197 =
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
               match uu____8197 with
               | (t12,t22) -> aux retry (n_delta + Prims.int_one) t12 t22  in
             let reduce_both_and_try_again d r1 =
               let uu____8245 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8245 with
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
                  uu____8283),uu____8284)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8305 =
                      let uu____8314 = maybe_inline t11  in
                      let uu____8317 = maybe_inline t21  in
                      (uu____8314, uu____8317)  in
                    match uu____8305 with
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
                 (uu____8360,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8361))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8382 =
                      let uu____8391 = maybe_inline t11  in
                      let uu____8394 = maybe_inline t21  in
                      (uu____8391, uu____8394)  in
                    match uu____8382 with
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
             | MisMatch uu____8449 -> fail n_delta r t11 t21
             | uu____8458 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8473 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8473
           then
             let uu____8478 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8480 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8482 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8490 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8507 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8507
                    (fun uu____8542  ->
                       match uu____8542 with
                       | (t11,t21) ->
                           let uu____8550 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8552 =
                             let uu____8554 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8554  in
                           Prims.op_Hat uu____8550 uu____8552))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8478 uu____8480 uu____8482 uu____8490
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8571 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8571 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8586  ->
    match uu___24_8586 with
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
      let uu___1215_8635 = p  in
      let uu____8638 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8639 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1215_8635.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8638;
        FStar_TypeChecker_Common.relation =
          (uu___1215_8635.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8639;
        FStar_TypeChecker_Common.element =
          (uu___1215_8635.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1215_8635.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1215_8635.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1215_8635.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1215_8635.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1215_8635.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8654 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8654
            (fun uu____8659  -> FStar_TypeChecker_Common.TProb uu____8659)
      | FStar_TypeChecker_Common.CProb uu____8660 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8683 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8683 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8691 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8691 with
           | (lh,lhs_args) ->
               let uu____8738 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8738 with
                | (rh,rhs_args) ->
                    let uu____8785 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8798,FStar_Syntax_Syntax.Tm_uvar uu____8799)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8888 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8915,uu____8916)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8931,FStar_Syntax_Syntax.Tm_uvar uu____8932)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8947,FStar_Syntax_Syntax.Tm_arrow uu____8948)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1266_8978 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1266_8978.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1266_8978.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1266_8978.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1266_8978.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1266_8978.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1266_8978.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1266_8978.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1266_8978.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1266_8978.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8981,FStar_Syntax_Syntax.Tm_type uu____8982)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1266_8998 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1266_8998.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1266_8998.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1266_8998.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1266_8998.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1266_8998.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1266_8998.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1266_8998.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1266_8998.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1266_8998.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9001,FStar_Syntax_Syntax.Tm_uvar uu____9002)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1266_9018 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1266_9018.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1266_9018.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1266_9018.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1266_9018.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1266_9018.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1266_9018.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1266_9018.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1266_9018.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1266_9018.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9021,FStar_Syntax_Syntax.Tm_uvar uu____9022)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9037,uu____9038)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9053,FStar_Syntax_Syntax.Tm_uvar uu____9054)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9069,uu____9070) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8785 with
                     | (rank,tp1) ->
                         let uu____9083 =
                           FStar_All.pipe_right
                             (let uu___1286_9087 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1286_9087.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1286_9087.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1286_9087.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1286_9087.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1286_9087.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1286_9087.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1286_9087.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1286_9087.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1286_9087.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____9090  ->
                                FStar_TypeChecker_Common.TProb uu____9090)
                            in
                         (rank, uu____9083))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9094 =
            FStar_All.pipe_right
              (let uu___1290_9098 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1290_9098.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1290_9098.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1290_9098.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1290_9098.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1290_9098.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1290_9098.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1290_9098.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1290_9098.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1290_9098.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____9101  -> FStar_TypeChecker_Common.CProb uu____9101)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9094)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9161 probs =
      match uu____9161 with
      | (min_rank,min,out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9242 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____9263 = rank wl.tcenv hd  in
               (match uu____9263 with
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
                      (let uu____9324 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9329 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9329)
                          in
                       if uu____9324
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
          let uu____9402 = FStar_Syntax_Util.head_and_args t  in
          match uu____9402 with
          | (hd,uu____9421) ->
              let uu____9446 =
                let uu____9447 = FStar_Syntax_Subst.compress hd  in
                uu____9447.FStar_Syntax_Syntax.n  in
              (match uu____9446 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9452) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9487  ->
                           match uu____9487 with
                           | (y,uu____9496) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9519  ->
                                       match uu____9519 with
                                       | (x,uu____9528) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9533 -> false)
           in
        let uu____9535 = rank tcenv p  in
        match uu____9535 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9544 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9625 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9644 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9663 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9680 = FStar_Thunk.mkv s  in UFailed uu____9680 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9695 = mklstr s  in UFailed uu____9695 
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
                        let uu____9746 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9746 with
                        | (k,uu____9754) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9767 -> false)))
            | uu____9769 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9821 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9829 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9829 = Prims.int_zero))
                           in
                        if uu____9821 then uv1 :: uvs else uvs) [])
               in
            let filter =
              FStar_List.filter
                (fun u  ->
                   let uu____9850 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9858 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9858 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9850)
               in
            let uu____9862 = filter u12  in
            let uu____9865 = filter u22  in (uu____9862, uu____9865)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9900 = filter_out_common_univs us1 us2  in
                   (match uu____9900 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9960 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9960 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9963 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9980  ->
                               let uu____9981 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____9983 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9981 uu____9983))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10009 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10009 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10035 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10035 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10038 ->
                   ufailed_thunk
                     (fun uu____10049  ->
                        let uu____10050 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10052 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10050 uu____10052 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10055,uu____10056) ->
              let uu____10058 =
                let uu____10060 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10062 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10060 uu____10062
                 in
              failwith uu____10058
          | (FStar_Syntax_Syntax.U_unknown ,uu____10065) ->
              let uu____10066 =
                let uu____10068 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10070 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10068 uu____10070
                 in
              failwith uu____10066
          | (uu____10073,FStar_Syntax_Syntax.U_bvar uu____10074) ->
              let uu____10076 =
                let uu____10078 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10080 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10078 uu____10080
                 in
              failwith uu____10076
          | (uu____10083,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10084 =
                let uu____10086 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10088 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10086 uu____10088
                 in
              failwith uu____10084
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              let uu____10093 =
                let uu____10095 = FStar_Ident.text_of_id x  in
                let uu____10097 = FStar_Ident.text_of_id y  in
                uu____10095 = uu____10097  in
              if uu____10093
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10124 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10124
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10141 = occurs_univ v1 u3  in
              if uu____10141
              then
                let uu____10144 =
                  let uu____10146 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10148 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10146 uu____10148
                   in
                try_umax_components u11 u21 uu____10144
              else
                (let uu____10153 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10153)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10165 = occurs_univ v1 u3  in
              if uu____10165
              then
                let uu____10168 =
                  let uu____10170 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10172 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10170 uu____10172
                   in
                try_umax_components u11 u21 uu____10168
              else
                (let uu____10177 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10177)
          | (FStar_Syntax_Syntax.U_max uu____10178,uu____10179) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10187 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10187
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10193,FStar_Syntax_Syntax.U_max uu____10194) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10202 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10202
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10208,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10210,FStar_Syntax_Syntax.U_name uu____10211) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10213) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10215) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10217,FStar_Syntax_Syntax.U_succ uu____10218) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10220,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10327 = bc1  in
      match uu____10327 with
      | (bs1,mk_cod1) ->
          let uu____10371 = bc2  in
          (match uu____10371 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10482 = aux xs ys  in
                     (match uu____10482 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10565 =
                       let uu____10572 = mk_cod1 xs  in ([], uu____10572)  in
                     let uu____10575 =
                       let uu____10582 = mk_cod2 ys  in ([], uu____10582)  in
                     (uu____10565, uu____10575)
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
                  let uu____10651 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10651 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10654 =
                    let uu____10655 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10655 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10654
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10660 = has_type_guard t1 t2  in (uu____10660, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10661 = has_type_guard t2 t1  in (uu____10661, wl)
  
let is_flex_pat :
  'uuuuuu10671 'uuuuuu10672 'uuuuuu10673 .
    ('uuuuuu10671 * 'uuuuuu10672 * 'uuuuuu10673 Prims.list) -> Prims.bool
  =
  fun uu___25_10687  ->
    match uu___25_10687 with
    | (uu____10696,uu____10697,[]) -> true
    | uu____10701 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10734 = f  in
      match uu____10734 with
      | (uu____10741,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10742;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10743;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10746;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10747;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10748;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10749;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10819  ->
                 match uu____10819 with
                 | (y,uu____10828) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10982 =
                  let uu____10997 =
                    let uu____11000 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11000  in
                  ((FStar_List.rev pat_binders), uu____10997)  in
                FStar_Pervasives_Native.Some uu____10982
            | (uu____11033,[]) ->
                let uu____11064 =
                  let uu____11079 =
                    let uu____11082 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11082  in
                  ((FStar_List.rev pat_binders), uu____11079)  in
                FStar_Pervasives_Native.Some uu____11064
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11173 =
                  let uu____11174 = FStar_Syntax_Subst.compress a  in
                  uu____11174.FStar_Syntax_Syntax.n  in
                (match uu____11173 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11194 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11194
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1618_11224 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1618_11224.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1618_11224.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst =
                          let uu____11228 =
                            let uu____11229 =
                              let uu____11236 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11236)  in
                            FStar_Syntax_Syntax.NT uu____11229  in
                          [uu____11228]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1  in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res  in
                        aux
                          (((let uu___1624_11252 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1624_11252.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1624_11252.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11253 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11293 =
                  let uu____11300 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11300  in
                (match uu____11293 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11359 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11384 ->
               let uu____11385 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11385 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11681 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11681
       then
         let uu____11686 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11686
       else ());
      (let uu____11692 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____11692
       then
         let uu____11697 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11697
       else ());
      (let uu____11702 = next_prob probs  in
       match uu____11702 with
       | FStar_Pervasives_Native.Some (hd,tl,rank1) ->
           let probs1 =
             let uu___1651_11729 = probs  in
             {
               attempting = tl;
               wl_deferred = (uu___1651_11729.wl_deferred);
               ctr = (uu___1651_11729.ctr);
               defer_ok = (uu___1651_11729.defer_ok);
               smt_ok = (uu___1651_11729.smt_ok);
               umax_heuristic_ok = (uu___1651_11729.umax_heuristic_ok);
               tcenv = (uu___1651_11729.tcenv);
               wl_implicits = (uu___1651_11729.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11738 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11738
                 then
                   let uu____11741 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1  in
                   solve env uu____11741
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
                       (let uu____11748 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd
                            probs1
                           in
                        solve env uu____11748)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1663_11754 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1663_11754.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1663_11754.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1663_11754.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1663_11754.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1663_11754.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1663_11754.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1663_11754.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1663_11754.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1663_11754.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11779 ->
                let uu____11789 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11854  ->
                          match uu____11854 with
                          | (c,uu____11864,uu____11865) -> c < probs.ctr))
                   in
                (match uu____11789 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11913 =
                            let uu____11918 =
                              FStar_List.map
                                (fun uu____11939  ->
                                   match uu____11939 with
                                   | (uu____11955,x,y) ->
                                       let uu____11966 = FStar_Thunk.force x
                                          in
                                       (uu____11966, y)) probs.wl_deferred
                               in
                            (uu____11918, (probs.wl_implicits))  in
                          Success uu____11913
                      | uu____11970 ->
                          let uu____11980 =
                            let uu___1681_11981 = probs  in
                            let uu____11982 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12003  ->
                                      match uu____12003 with
                                      | (uu____12011,uu____12012,y) -> y))
                               in
                            {
                              attempting = uu____11982;
                              wl_deferred = rest;
                              ctr = (uu___1681_11981.ctr);
                              defer_ok = (uu___1681_11981.defer_ok);
                              smt_ok = (uu___1681_11981.smt_ok);
                              umax_heuristic_ok =
                                (uu___1681_11981.umax_heuristic_ok);
                              tcenv = (uu___1681_11981.tcenv);
                              wl_implicits = (uu___1681_11981.wl_implicits)
                            }  in
                          solve env uu____11980))))

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
            let uu____12021 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12021 with
            | USolved wl1 ->
                let uu____12023 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12023
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12026 = defer_lit "" orig wl1  in
                solve env uu____12026

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
                  let uu____12077 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12077 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12080 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12093;
                  FStar_Syntax_Syntax.vars = uu____12094;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12097;
                  FStar_Syntax_Syntax.vars = uu____12098;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12111,uu____12112) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12120,FStar_Syntax_Syntax.Tm_uinst uu____12121) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12129 -> USolved wl

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
            ((let uu____12140 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12140
              then
                let uu____12145 = prob_to_string env orig  in
                let uu____12147 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12145 uu____12147
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
               let uu____12240 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12240 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12295 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12295
                then
                  let uu____12300 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12302 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12300 uu____12302
                else ());
               (let uu____12307 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12307 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12353 = eq_prob t1 t2 wl2  in
                         (match uu____12353 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12374 ->
                         let uu____12383 = eq_prob t1 t2 wl2  in
                         (match uu____12383 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12433 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12448 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12449 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12448, uu____12449)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12454 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12455 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12454, uu____12455)
                            in
                         (match uu____12433 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12486 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12486 with
                                | (t1_hd,t1_args) ->
                                    let uu____12531 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12531 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12597 =
                                              let uu____12604 =
                                                let uu____12615 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12615 :: t1_args  in
                                              let uu____12632 =
                                                let uu____12641 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12641 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12690  ->
                                                   fun uu____12691  ->
                                                     fun uu____12692  ->
                                                       match (uu____12690,
                                                               uu____12691,
                                                               uu____12692)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12742),
                                                          (a2,uu____12744))
                                                           ->
                                                           let uu____12781 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12781
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12604
                                                uu____12632
                                               in
                                            match uu____12597 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1835_12807 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1835_12807.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1835_12807.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1835_12807.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12818 =
                                                  solve env1 wl'  in
                                                (match uu____12818 with
                                                 | Success (uu____12821,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1844_12825
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1844_12825.attempting);
                                                            wl_deferred =
                                                              (uu___1844_12825.wl_deferred);
                                                            ctr =
                                                              (uu___1844_12825.ctr);
                                                            defer_ok =
                                                              (uu___1844_12825.defer_ok);
                                                            smt_ok =
                                                              (uu___1844_12825.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1844_12825.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1844_12825.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12826 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12858 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12858 with
                                | (t1_base,p1_opt) ->
                                    let uu____12894 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12894 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____12993 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____12993
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
                                               let uu____13046 =
                                                 op phi11 phi21  in
                                               refine x1 uu____13046
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
                                               let uu____13078 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13078
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
                                               let uu____13110 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13110
                                           | uu____13113 -> t_base  in
                                         let uu____13130 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13130 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13144 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13144, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13151 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13151 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13187 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13187 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13223 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13223
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
                              let uu____13247 = combine t11 t21 wl2  in
                              (match uu____13247 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13280 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13280
                                     then
                                       let uu____13285 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13285
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13327 ts1 =
               match uu____13327 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13390 = pairwise out t wl2  in
                        (match uu____13390 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13426 =
               let uu____13437 = FStar_List.hd ts  in (uu____13437, [], wl1)
                in
             let uu____13446 = FStar_List.tl ts  in
             aux uu____13426 uu____13446  in
           let uu____13453 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13453 with
           | (this_flex,this_rigid) ->
               let uu____13479 =
                 let uu____13480 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13480.FStar_Syntax_Syntax.n  in
               (match uu____13479 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13505 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13505
                    then
                      let uu____13508 = destruct_flex_t this_flex wl  in
                      (match uu____13508 with
                       | (flex,wl1) ->
                           let uu____13515 = quasi_pattern env flex  in
                           (match uu____13515 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t1)
                                ->
                                ((let uu____13534 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13534
                                  then
                                    let uu____13539 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13539
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13546 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1946_13549 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1946_13549.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1946_13549.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1946_13549.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1946_13549.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1946_13549.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1946_13549.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1946_13549.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1946_13549.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1946_13549.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13546)
                | uu____13550 ->
                    ((let uu____13552 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13552
                      then
                        let uu____13557 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13557
                      else ());
                     (let uu____13562 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13562 with
                      | (u,_args) ->
                          let uu____13605 =
                            let uu____13606 = FStar_Syntax_Subst.compress u
                               in
                            uu____13606.FStar_Syntax_Syntax.n  in
                          (match uu____13605 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv t =
                                 let uu____13634 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13634 with
                                 | (u',uu____13653) ->
                                     let uu____13678 =
                                       let uu____13679 = whnf env u'  in
                                       uu____13679.FStar_Syntax_Syntax.n  in
                                     (match uu____13678 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13701 -> false)
                                  in
                               let uu____13703 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13726  ->
                                         match uu___26_13726 with
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
                                              | uu____13740 -> false)
                                         | uu____13744 -> false))
                                  in
                               (match uu____13703 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13759 = whnf env this_rigid
                                         in
                                      let uu____13760 =
                                        FStar_List.collect
                                          (fun uu___27_13766  ->
                                             match uu___27_13766 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13772 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13772]
                                             | uu____13776 -> [])
                                          bounds_probs
                                         in
                                      uu____13759 :: uu____13760  in
                                    let uu____13777 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13777 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13810 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13825 =
                                               let uu____13826 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13826.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13825 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13838 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13838)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13849 -> bound  in
                                           let uu____13850 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13850)  in
                                         (match uu____13810 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13885 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13885
                                                then
                                                  let wl'1 =
                                                    let uu___2006_13891 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2006_13891.wl_deferred);
                                                      ctr =
                                                        (uu___2006_13891.ctr);
                                                      defer_ok =
                                                        (uu___2006_13891.defer_ok);
                                                      smt_ok =
                                                        (uu___2006_13891.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2006_13891.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2006_13891.tcenv);
                                                      wl_implicits =
                                                        (uu___2006_13891.wl_implicits)
                                                    }  in
                                                  let uu____13892 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13892
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13898 =
                                                  solve_t env eq_prob
                                                    (let uu___2011_13900 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2011_13900.wl_deferred);
                                                       ctr =
                                                         (uu___2011_13900.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2011_13900.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2011_13900.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2011_13900.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13898 with
                                                | Success (uu____13902,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2017_13905 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2017_13905.wl_deferred);
                                                        ctr =
                                                          (uu___2017_13905.ctr);
                                                        defer_ok =
                                                          (uu___2017_13905.defer_ok);
                                                        smt_ok =
                                                          (uu___2017_13905.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2017_13905.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2017_13905.tcenv);
                                                        wl_implicits =
                                                          (uu___2017_13905.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2020_13907 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2020_13907.attempting);
                                                        wl_deferred =
                                                          (uu___2020_13907.wl_deferred);
                                                        ctr =
                                                          (uu___2020_13907.ctr);
                                                        defer_ok =
                                                          (uu___2020_13907.defer_ok);
                                                        smt_ok =
                                                          (uu___2020_13907.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2020_13907.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2020_13907.tcenv);
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
                                                    let uu____13923 =
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
                                                    ((let uu____13935 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13935
                                                      then
                                                        let uu____13940 =
                                                          let uu____13942 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13942
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13940
                                                      else ());
                                                     (let uu____13955 =
                                                        let uu____13970 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13970)
                                                         in
                                                      match uu____13955 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____13992))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14018 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14018
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
                                                                  let uu____14038
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14038))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14063 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14063
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
                                                                    let uu____14083
                                                                    =
                                                                    let uu____14088
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14088
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14083
                                                                    [] wl2
                                                                     in
                                                                  let uu____14094
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14094))))
                                                      | uu____14095 ->
                                                          let uu____14110 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14110 p)))))))
                           | uu____14117 when flip ->
                               let uu____14118 =
                                 let uu____14120 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14122 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14120 uu____14122
                                  in
                               failwith uu____14118
                           | uu____14125 ->
                               let uu____14126 =
                                 let uu____14128 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14130 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14128 uu____14130
                                  in
                               failwith uu____14126)))))

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
                      (fun uu____14166  ->
                         match uu____14166 with
                         | (x,i) ->
                             let uu____14185 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14185, i)) bs_lhs
                     in
                  let uu____14188 = lhs  in
                  match uu____14188 with
                  | (uu____14189,u_lhs,uu____14191) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14288 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14298 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14298, univ)
                             in
                          match uu____14288 with
                          | (k,univ) ->
                              let uu____14305 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14305 with
                               | (uu____14322,u,wl3) ->
                                   let uu____14325 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14325, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14351 =
                              let uu____14364 =
                                let uu____14375 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14375 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14426  ->
                                   fun uu____14427  ->
                                     match (uu____14426, uu____14427) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14528 =
                                           let uu____14535 =
                                             let uu____14538 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14538
                                              in
                                           copy_uvar u_lhs [] uu____14535 wl2
                                            in
                                         (match uu____14528 with
                                          | (uu____14567,t_a,wl3) ->
                                              let uu____14570 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14570 with
                                               | (uu____14589,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14364
                                ([], wl1)
                               in
                            (match uu____14351 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2131_14645 = ct  in
                                   let uu____14646 =
                                     let uu____14649 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14649
                                      in
                                   let uu____14664 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2131_14645.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2131_14645.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14646;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14664;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2131_14645.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2134_14682 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2134_14682.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2134_14682.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14685 =
                        FStar_Syntax_Util.arrow_formals_comp arrow  in
                      (match uu____14685 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14723 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14723 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14734 =
                                          let uu____14739 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14739)  in
                                        TERM uu____14734  in
                                      let uu____14740 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14740 with
                                       | (sub_prob,wl3) ->
                                           let uu____14754 =
                                             let uu____14755 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14755
                                              in
                                           solve env uu____14754))
                             | (x,imp)::formals2 ->
                                 let uu____14777 =
                                   let uu____14784 =
                                     let uu____14787 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14787
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14784 wl1
                                    in
                                 (match uu____14777 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14808 =
                                          let uu____14811 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14811
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14808 u_x
                                         in
                                      let uu____14812 =
                                        let uu____14815 =
                                          let uu____14818 =
                                            let uu____14819 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14819, imp)  in
                                          [uu____14818]  in
                                        FStar_List.append bs_terms
                                          uu____14815
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14812 formals2 wl2)
                              in
                           let uu____14846 = occurs_check u_lhs arrow  in
                           (match uu____14846 with
                            | (uu____14859,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14875 =
                                    mklstr
                                      (fun uu____14880  ->
                                         let uu____14881 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14881)
                                     in
                                  giveup_or_defer env orig wl uu____14875
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
              (let uu____14914 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14914
               then
                 let uu____14919 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14922 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14919 (rel_to_string (p_rel orig)) uu____14922
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15053 = rhs wl1 scope env1 subst  in
                     (match uu____15053 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15076 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15076
                            then
                              let uu____15081 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15081
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15159 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15159 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2204_15161 = hd1  in
                       let uu____15162 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2204_15161.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2204_15161.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15162
                       }  in
                     let hd21 =
                       let uu___2207_15166 = hd2  in
                       let uu____15167 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2207_15166.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2207_15166.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15167
                       }  in
                     let uu____15170 =
                       let uu____15175 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15175
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15170 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst1 =
                            let uu____15198 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15198
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15205 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1
                             in
                          (match uu____15205 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15277 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15277
                                  in
                               ((let uu____15295 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15295
                                 then
                                   let uu____15300 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15302 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15300
                                     uu____15302
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____15337 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15373 = aux wl [] env [] bs1 bs2  in
               match uu____15373 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15432 = attempt sub_probs wl2  in
                   solve env1 uu____15432)

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
            let uu___2245_15452 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2245_15452.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2245_15452.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15464 = try_solve env wl'  in
          match uu____15464 with
          | Success (uu____15465,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2254_15469 = wl  in
                  {
                    attempting = (uu___2254_15469.attempting);
                    wl_deferred = (uu___2254_15469.wl_deferred);
                    ctr = (uu___2254_15469.ctr);
                    defer_ok = (uu___2254_15469.defer_ok);
                    smt_ok = (uu___2254_15469.smt_ok);
                    umax_heuristic_ok = (uu___2254_15469.umax_heuristic_ok);
                    tcenv = (uu___2254_15469.tcenv);
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
        (let uu____15478 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15478 wl)

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
              let uu____15492 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15492 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15526 = lhs1  in
              match uu____15526 with
              | (uu____15529,ctx_u,uu____15531) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15539 ->
                        let uu____15540 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15540 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15589 = quasi_pattern env1 lhs1  in
              match uu____15589 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15623) ->
                  let uu____15628 = lhs1  in
                  (match uu____15628 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15643 = occurs_check ctx_u rhs1  in
                       (match uu____15643 with
                        | (uvars,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15694 =
                                let uu____15702 =
                                  let uu____15704 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15704
                                   in
                                FStar_Util.Inl uu____15702  in
                              (uu____15694, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15732 =
                                 let uu____15734 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15734  in
                               if uu____15732
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15761 =
                                    let uu____15769 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15769  in
                                  let uu____15775 =
                                    restrict_all_uvars ctx_u uvars wl1  in
                                  (uu____15761, uu____15775)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15819 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15819 with
              | (rhs_hd,args) ->
                  let uu____15862 = FStar_Util.prefix args  in
                  (match uu____15862 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15934 = lhs1  in
                       (match uu____15934 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15938 =
                              let uu____15949 =
                                let uu____15956 =
                                  let uu____15959 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15959
                                   in
                                copy_uvar u_lhs [] uu____15956 wl1  in
                              match uu____15949 with
                              | (uu____15986,t_last_arg,wl2) ->
                                  let uu____15989 =
                                    let uu____15996 =
                                      let uu____15997 =
                                        let uu____16006 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____16006]  in
                                      FStar_List.append bs_lhs uu____15997
                                       in
                                    copy_uvar u_lhs uu____15996 t_res_lhs wl2
                                     in
                                  (match uu____15989 with
                                   | (uu____16041,lhs',wl3) ->
                                       let uu____16044 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16044 with
                                        | (uu____16061,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15938 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16082 =
                                     let uu____16083 =
                                       let uu____16088 =
                                         let uu____16089 =
                                           let uu____16092 =
                                             let uu____16097 =
                                               let uu____16098 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16098]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16097
                                              in
                                           uu____16092
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16089
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16088)  in
                                     TERM uu____16083  in
                                   [uu____16082]  in
                                 let uu____16123 =
                                   let uu____16130 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16130 with
                                   | (p1,wl3) ->
                                       let uu____16150 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16150 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16123 with
                                  | (sub_probs,wl3) ->
                                      let uu____16182 =
                                        let uu____16183 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16183  in
                                      solve env1 uu____16182))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16217 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16217 with
                | (uu____16235,args) ->
                    (match args with | [] -> false | uu____16271 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16290 =
                  let uu____16291 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16291.FStar_Syntax_Syntax.n  in
                match uu____16290 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16295 -> true
                | uu____16311 -> false  in
              let uu____16313 = quasi_pattern env1 lhs1  in
              match uu____16313 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    mklstr
                      (fun uu____16332  ->
                         let uu____16333 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16333)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16342 = is_app rhs1  in
                  if uu____16342
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16347 = is_arrow rhs1  in
                     if uu____16347
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          mklstr
                            (fun uu____16360  ->
                               let uu____16361 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16361)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16365 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16365
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16371 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16371
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16376 = lhs  in
                (match uu____16376 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16380 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16380 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16398 =
                              let uu____16402 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16402
                               in
                            FStar_All.pipe_right uu____16398
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16423 = occurs_check ctx_uv rhs1  in
                          (match uu____16423 with
                           | (uvars,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16452 =
                                   let uu____16453 =
                                     let uu____16455 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16455
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16453
                                    in
                                 giveup_or_defer env orig wl uu____16452
                               else
                                 (let uu____16463 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16463
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars wl  in
                                    let uu____16470 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16470
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         mklstr
                                           (fun uu____16486  ->
                                              let uu____16487 =
                                                names_to_string1 fvs2  in
                                              let uu____16489 =
                                                names_to_string1 fvs1  in
                                              let uu____16491 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16487 uu____16489
                                                uu____16491)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16503 ->
                          if wl.defer_ok
                          then
                            let uu____16507 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16507
                          else
                            (let uu____16512 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16512 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16538 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16538
                             | (FStar_Util.Inl msg,uu____16540) ->
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
                  let uu____16558 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16558
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16564 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16564
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16586 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16586
                else
                  (let uu____16591 =
                     let uu____16608 = quasi_pattern env lhs  in
                     let uu____16615 = quasi_pattern env rhs  in
                     (uu____16608, uu____16615)  in
                   match uu____16591 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16658 = lhs  in
                       (match uu____16658 with
                        | ({ FStar_Syntax_Syntax.n = uu____16659;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16661;_},u_lhs,uu____16663)
                            ->
                            let uu____16666 = rhs  in
                            (match uu____16666 with
                             | (uu____16667,u_rhs,uu____16669) ->
                                 let uu____16670 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16670
                                 then
                                   let uu____16677 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16677
                                 else
                                   (let uu____16680 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16680 with
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
                                        let uu____16712 =
                                          let uu____16719 =
                                            let uu____16722 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16722
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16719
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16712 with
                                         | (uu____16734,w,wl1) ->
                                             let w_app =
                                               let uu____16740 =
                                                 let uu____16745 =
                                                   FStar_List.map
                                                     (fun uu____16756  ->
                                                        match uu____16756
                                                        with
                                                        | (z,uu____16764) ->
                                                            let uu____16769 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16769) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16745
                                                  in
                                               uu____16740
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16771 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16771
                                               then
                                                 let uu____16776 =
                                                   let uu____16780 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16782 =
                                                     let uu____16786 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16788 =
                                                       let uu____16792 =
                                                         term_to_string w  in
                                                       let uu____16794 =
                                                         let uu____16798 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16807 =
                                                           let uu____16811 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16820 =
                                                             let uu____16824
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16824]
                                                              in
                                                           uu____16811 ::
                                                             uu____16820
                                                            in
                                                         uu____16798 ::
                                                           uu____16807
                                                          in
                                                       uu____16792 ::
                                                         uu____16794
                                                        in
                                                     uu____16786 ::
                                                       uu____16788
                                                      in
                                                   uu____16780 :: uu____16782
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16776
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16841 =
                                                     let uu____16846 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16846)  in
                                                   TERM uu____16841  in
                                                 let uu____16847 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16847
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16855 =
                                                        let uu____16860 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16860)
                                                         in
                                                      TERM uu____16855  in
                                                    [s1; s2])
                                                  in
                                               let uu____16861 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16861))))))
                   | uu____16862 ->
                       let uu____16879 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16879)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16933 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16933
            then
              let uu____16938 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16940 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16942 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16944 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16938 uu____16940 uu____16942 uu____16944
            else ());
           (let uu____16955 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16955 with
            | (head1,args1) ->
                let uu____16998 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____16998 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17068 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17068 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17073 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17073)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17094 =
                         mklstr
                           (fun uu____17105  ->
                              let uu____17106 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17108 = args_to_string args1  in
                              let uu____17112 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17114 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17106 uu____17108 uu____17112
                                uu____17114)
                          in
                       giveup env1 uu____17094 orig
                     else
                       (let uu____17121 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17126 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17126 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17121
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2510_17130 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2510_17130.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2510_17130.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2510_17130.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2510_17130.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2510_17130.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2510_17130.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2510_17130.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2510_17130.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17140 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17140
                                    else solve env1 wl2))
                        else
                          (let uu____17145 = base_and_refinement env1 t1  in
                           match uu____17145 with
                           | (base1,refinement1) ->
                               let uu____17170 = base_and_refinement env1 t2
                                  in
                               (match uu____17170 with
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
                                           let uu____17335 =
                                             FStar_List.fold_right
                                               (fun uu____17375  ->
                                                  fun uu____17376  ->
                                                    match (uu____17375,
                                                            uu____17376)
                                                    with
                                                    | (((a1,uu____17428),
                                                        (a2,uu____17430)),
                                                       (probs,wl3)) ->
                                                        let uu____17479 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17479
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17335 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17522 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17522
                                                 then
                                                   let uu____17527 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17527
                                                 else ());
                                                (let uu____17533 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17533
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
                                                    (let uu____17560 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17560 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17576 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17576
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17584 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17584))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17609 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17609 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17625 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17625
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17633 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17633)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17661 =
                                           match uu____17661 with
                                           | (prob,reason) ->
                                               ((let uu____17678 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17678
                                                 then
                                                   let uu____17683 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17685 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____17683 uu____17685
                                                 else ());
                                                (let uu____17691 =
                                                   let uu____17700 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17703 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17700, uu____17703)
                                                    in
                                                 match uu____17691 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17716 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17716 with
                                                      | (head1',uu____17734)
                                                          ->
                                                          let uu____17759 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17759
                                                           with
                                                           | (head2',uu____17777)
                                                               ->
                                                               let uu____17802
                                                                 =
                                                                 let uu____17807
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17808
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17807,
                                                                   uu____17808)
                                                                  in
                                                               (match uu____17802
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
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
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17817
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17819
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17821
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17815
                                                                    uu____17817
                                                                    uu____17819
                                                                    uu____17821
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17826
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2598_17834
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2598_17834.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2598_17834.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2598_17834.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2598_17834.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2598_17834.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2598_17834.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2598_17834.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2598_17834.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17836
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17836
                                                                    then
                                                                    let uu____17841
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17841
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17846 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17858 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17858 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17866 =
                                             let uu____17867 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17867.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17866 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17872 -> false  in
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
                                          | uu____17875 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17878 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2618_17914 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2618_17914.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2618_17914.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2618_17914.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2618_17914.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2618_17914.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2618_17914.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2618_17914.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2618_17914.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17990 = destruct_flex_t scrutinee wl1  in
             match uu____17990 with
             | ((_t,uv,_args),wl2) ->
                 let uu____18001 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18001 with
                  | (xs,pat_term,uu____18017,uu____18018) ->
                      let uu____18023 =
                        FStar_List.fold_left
                          (fun uu____18046  ->
                             fun x  ->
                               match uu____18046 with
                               | (subst,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18067 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18067 with
                                    | (uu____18086,u,wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst  in
                                        (subst1, wl4))) ([], wl2) xs
                         in
                      (match uu____18023 with
                       | (subst,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term  in
                           let uu____18107 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18107 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2658_18124 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2658_18124.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2658_18124.umax_heuristic_ok);
                                    tcenv = (uu___2658_18124.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18135 = solve env1 wl'  in
                                (match uu____18135 with
                                 | Success (uu____18138,imps) ->
                                     let wl'1 =
                                       let uu___2666_18141 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2666_18141.wl_deferred);
                                         ctr = (uu___2666_18141.ctr);
                                         defer_ok =
                                           (uu___2666_18141.defer_ok);
                                         smt_ok = (uu___2666_18141.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2666_18141.umax_heuristic_ok);
                                         tcenv = (uu___2666_18141.tcenv);
                                         wl_implicits =
                                           (uu___2666_18141.wl_implicits)
                                       }  in
                                     let uu____18142 = solve env1 wl'1  in
                                     (match uu____18142 with
                                      | Success (uu____18145,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2674_18149 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2674_18149.attempting);
                                                 wl_deferred =
                                                   (uu___2674_18149.wl_deferred);
                                                 ctr = (uu___2674_18149.ctr);
                                                 defer_ok =
                                                   (uu___2674_18149.defer_ok);
                                                 smt_ok =
                                                   (uu___2674_18149.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2674_18149.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2674_18149.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18150 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18156 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18179 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18179
                 then
                   let uu____18184 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18186 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18184 uu____18186
                 else ());
                (let uu____18191 =
                   let uu____18212 =
                     let uu____18221 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18221)  in
                   let uu____18228 =
                     let uu____18237 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18237)  in
                   (uu____18212, uu____18228)  in
                 match uu____18191 with
                 | ((uu____18267,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18270;
                                   FStar_Syntax_Syntax.vars = uu____18271;_}),
                    (s,t)) ->
                     let uu____18342 =
                       let uu____18344 = is_flex scrutinee  in
                       Prims.op_Negation uu____18344  in
                     if uu____18342
                     then
                       ((let uu____18355 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18355
                         then
                           let uu____18360 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18360
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18379 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18379
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18394 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18394
                           then
                             let uu____18399 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18401 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18399 uu____18401
                           else ());
                          (let pat_discriminates uu___28_18426 =
                             match uu___28_18426 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18442;
                                  FStar_Syntax_Syntax.p = uu____18443;_},FStar_Pervasives_Native.None
                                ,uu____18444) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18458;
                                  FStar_Syntax_Syntax.p = uu____18459;_},FStar_Pervasives_Native.None
                                ,uu____18460) -> true
                             | uu____18487 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18590 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18590 with
                                       | (uu____18592,uu____18593,t') ->
                                           let uu____18611 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18611 with
                                            | (FullMatch ,uu____18623) ->
                                                true
                                            | (HeadMatch
                                               uu____18637,uu____18638) ->
                                                true
                                            | uu____18653 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18690 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18690
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18701 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18701 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18789,uu____18790) ->
                                       branches1
                                   | uu____18935 -> branches  in
                                 let uu____18990 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____18999 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____18999 with
                                        | (p,uu____19003,uu____19004) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19033  ->
                                      FStar_Util.Inr uu____19033) uu____18990))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19063 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19063 with
                                | (p,uu____19072,e) ->
                                    ((let uu____19091 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19091
                                      then
                                        let uu____19096 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19098 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19096 uu____19098
                                      else ());
                                     (let uu____19103 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____19118  ->
                                           FStar_Util.Inr uu____19118)
                                        uu____19103)))))
                 | ((s,t),(uu____19121,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19124;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19125;_}))
                     ->
                     let uu____19194 =
                       let uu____19196 = is_flex scrutinee  in
                       Prims.op_Negation uu____19196  in
                     if uu____19194
                     then
                       ((let uu____19207 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19207
                         then
                           let uu____19212 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19212
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19231 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19231
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19246 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19246
                           then
                             let uu____19251 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19253 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19251 uu____19253
                           else ());
                          (let pat_discriminates uu___28_19278 =
                             match uu___28_19278 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19294;
                                  FStar_Syntax_Syntax.p = uu____19295;_},FStar_Pervasives_Native.None
                                ,uu____19296) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19310;
                                  FStar_Syntax_Syntax.p = uu____19311;_},FStar_Pervasives_Native.None
                                ,uu____19312) -> true
                             | uu____19339 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19442 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19442 with
                                       | (uu____19444,uu____19445,t') ->
                                           let uu____19463 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19463 with
                                            | (FullMatch ,uu____19475) ->
                                                true
                                            | (HeadMatch
                                               uu____19489,uu____19490) ->
                                                true
                                            | uu____19505 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19542 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19542
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19553 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19553 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19641,uu____19642) ->
                                       branches1
                                   | uu____19787 -> branches  in
                                 let uu____19842 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19851 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19851 with
                                        | (p,uu____19855,uu____19856) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19885  ->
                                      FStar_Util.Inr uu____19885) uu____19842))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19915 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19915 with
                                | (p,uu____19924,e) ->
                                    ((let uu____19943 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19943
                                      then
                                        let uu____19948 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19950 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19948 uu____19950
                                      else ());
                                     (let uu____19955 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____19970  ->
                                           FStar_Util.Inr uu____19970)
                                        uu____19955)))))
                 | uu____19971 ->
                     ((let uu____19993 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19993
                       then
                         let uu____19998 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20000 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____19998 uu____20000
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20046 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20046
            then
              let uu____20051 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20053 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20055 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20057 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20051 uu____20053 uu____20055 uu____20057
            else ());
           (let uu____20062 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20062 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20093,uu____20094) ->
                     let rec may_relate head =
                       let uu____20122 =
                         let uu____20123 = FStar_Syntax_Subst.compress head
                            in
                         uu____20123.FStar_Syntax_Syntax.n  in
                       match uu____20122 with
                       | FStar_Syntax_Syntax.Tm_name uu____20127 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20129 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20154 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20154 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20156 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20159
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20160 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20163,uu____20164) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20206) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20212) ->
                           may_relate t
                       | uu____20217 -> false  in
                     let uu____20219 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20219 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20232 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20232
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20242 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20242
                          then
                            let uu____20245 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20245 with
                             | (guard,wl2) ->
                                 let uu____20252 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20252)
                          else
                            (let uu____20255 =
                               mklstr
                                 (fun uu____20266  ->
                                    let uu____20267 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20269 =
                                      let uu____20271 =
                                        let uu____20275 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20275
                                          (fun x  ->
                                             let uu____20282 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20282)
                                         in
                                      FStar_Util.dflt "" uu____20271  in
                                    let uu____20287 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20289 =
                                      let uu____20291 =
                                        let uu____20295 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20295
                                          (fun x  ->
                                             let uu____20302 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20302)
                                         in
                                      FStar_Util.dflt "" uu____20291  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20267 uu____20269 uu____20287
                                      uu____20289)
                                in
                             giveup env1 uu____20255 orig))
                 | (HeadMatch (true ),uu____20308) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20323 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20323 with
                        | (guard,wl2) ->
                            let uu____20330 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20330)
                     else
                       (let uu____20333 =
                          mklstr
                            (fun uu____20340  ->
                               let uu____20341 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20343 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20341 uu____20343)
                           in
                        giveup env1 uu____20333 orig)
                 | (uu____20346,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2849_20360 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2849_20360.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2849_20360.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2849_20360.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2849_20360.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2849_20360.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2849_20360.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2849_20360.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2849_20360.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20387 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20387
          then
            let uu____20390 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20390
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20396 =
                let uu____20399 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20399  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20396 t1);
             (let uu____20418 =
                let uu____20421 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20421  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20418 t2);
             (let uu____20440 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20440
              then
                let uu____20444 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20446 =
                  let uu____20448 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20450 =
                    let uu____20452 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20452  in
                  Prims.op_Hat uu____20448 uu____20450  in
                let uu____20455 =
                  let uu____20457 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20459 =
                    let uu____20461 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20461  in
                  Prims.op_Hat uu____20457 uu____20459  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20444 uu____20446 uu____20455
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20468,uu____20469) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20485,FStar_Syntax_Syntax.Tm_delayed uu____20486) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20502,uu____20503) ->
                  let uu____20530 =
                    let uu___2880_20531 = problem  in
                    let uu____20532 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2880_20531.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20532;
                      FStar_TypeChecker_Common.relation =
                        (uu___2880_20531.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2880_20531.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2880_20531.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2880_20531.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2880_20531.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2880_20531.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2880_20531.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2880_20531.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20530 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20533,uu____20534) ->
                  let uu____20541 =
                    let uu___2886_20542 = problem  in
                    let uu____20543 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2886_20542.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20543;
                      FStar_TypeChecker_Common.relation =
                        (uu___2886_20542.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2886_20542.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2886_20542.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2886_20542.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2886_20542.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2886_20542.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2886_20542.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2886_20542.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20541 wl
              | (uu____20544,FStar_Syntax_Syntax.Tm_ascribed uu____20545) ->
                  let uu____20572 =
                    let uu___2892_20573 = problem  in
                    let uu____20574 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2892_20573.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2892_20573.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2892_20573.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20574;
                      FStar_TypeChecker_Common.element =
                        (uu___2892_20573.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2892_20573.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2892_20573.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2892_20573.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2892_20573.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2892_20573.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20572 wl
              | (uu____20575,FStar_Syntax_Syntax.Tm_meta uu____20576) ->
                  let uu____20583 =
                    let uu___2898_20584 = problem  in
                    let uu____20585 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2898_20584.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2898_20584.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2898_20584.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20585;
                      FStar_TypeChecker_Common.element =
                        (uu___2898_20584.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2898_20584.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2898_20584.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2898_20584.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2898_20584.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2898_20584.FStar_TypeChecker_Common.rank)
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
                                fun subst  ->
                                  let c12 =
                                    FStar_Syntax_Subst.subst_comp subst c11
                                     in
                                  let c22 =
                                    FStar_Syntax_Subst.subst_comp subst c21
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
                                fun subst  ->
                                  let uu____21137 =
                                    FStar_Syntax_Subst.subst subst tbody11
                                     in
                                  let uu____21138 =
                                    FStar_Syntax_Subst.subst subst tbody21
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
                           (let uu___3000_21260 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3000_21260.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3000_21260.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3000_21260.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3000_21260.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3000_21260.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3000_21260.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3000_21260.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3000_21260.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3000_21260.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3000_21260.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3000_21260.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3000_21260.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3000_21260.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3000_21260.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3000_21260.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3000_21260.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3000_21260.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3000_21260.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3000_21260.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3000_21260.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3000_21260.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3000_21260.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3000_21260.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3000_21260.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3000_21260.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3000_21260.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3000_21260.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3000_21260.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3000_21260.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3000_21260.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3000_21260.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3000_21260.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3000_21260.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3000_21260.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3000_21260.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3000_21260.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3000_21260.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3000_21260.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3000_21260.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3000_21260.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3000_21260.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3000_21260.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3000_21260.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3000_21260.FStar_TypeChecker_Env.erasable_types_tab)
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
                         (let uu___3021_21372 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3021_21372.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3021_21372.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3021_21372.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3021_21372.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3021_21372.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3021_21372.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3021_21372.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3021_21372.FStar_TypeChecker_Common.rank)
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
                              (let uu___3038_21413 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21413.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21413.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21413.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21413.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21413.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21413.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21413.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21413.FStar_TypeChecker_Common.rank)
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
                              (let uu___3038_21459 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21459.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21459.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21459.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21459.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21459.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21459.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21459.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21459.FStar_TypeChecker_Common.rank)
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
                           (let uu___3000_21603 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3000_21603.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3000_21603.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3000_21603.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3000_21603.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3000_21603.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3000_21603.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3000_21603.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3000_21603.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3000_21603.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3000_21603.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3000_21603.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3000_21603.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3000_21603.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3000_21603.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3000_21603.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3000_21603.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3000_21603.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3000_21603.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3000_21603.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3000_21603.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3000_21603.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3000_21603.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3000_21603.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3000_21603.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3000_21603.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3000_21603.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3000_21603.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3000_21603.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3000_21603.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3000_21603.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3000_21603.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3000_21603.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3000_21603.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3000_21603.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3000_21603.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3000_21603.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3000_21603.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3000_21603.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3000_21603.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3000_21603.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3000_21603.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3000_21603.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3000_21603.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3000_21603.FStar_TypeChecker_Env.erasable_types_tab)
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
                         (let uu___3021_21715 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3021_21715.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3021_21715.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3021_21715.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3021_21715.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3021_21715.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3021_21715.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3021_21715.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3021_21715.FStar_TypeChecker_Common.rank)
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
                              (let uu___3038_21756 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21756.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21756.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21756.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21756.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21756.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21756.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21756.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21756.FStar_TypeChecker_Common.rank)
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
                              (let uu___3038_21802 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21802.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21802.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21802.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21802.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21802.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21802.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21802.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21802.FStar_TypeChecker_Common.rank)
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
                        ((let uu___3061_21871 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3061_21871.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3061_21871.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3063_21873 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3063_21873.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3063_21873.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21874,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3061_21889 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3061_21889.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3061_21889.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3063_21891 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3063_21891.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3063_21891.FStar_Syntax_Syntax.index);
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
                                                  (let uu___3106_22145 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3106_22145.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3106_22145.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3106_22145.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3106_22145.tcenv);
                                                     wl_implicits =
                                                       (uu___3106_22145.wl_implicits)
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
                                                       let uu___3119_22178 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3119_22178.attempting);
                                                         wl_deferred =
                                                           (uu___3119_22178.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3119_22178.defer_ok);
                                                         smt_ok =
                                                           (uu___3119_22178.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3119_22178.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3119_22178.tcenv);
                                                         wl_implicits =
                                                           (uu___3119_22178.wl_implicits)
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
                    (let uu___3219_22604 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3219_22604.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3219_22604.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3219_22604.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3219_22604.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3219_22604.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3219_22604.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3219_22604.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3219_22604.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3219_22604.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22605;
                    FStar_Syntax_Syntax.pos = uu____22606;
                    FStar_Syntax_Syntax.vars = uu____22607;_},uu____22608),FStar_Syntax_Syntax.Tm_arrow
                 uu____22609) ->
                  solve_t' env
                    (let uu___3219_22661 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3219_22661.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3219_22661.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3219_22661.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3219_22661.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3219_22661.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3219_22661.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3219_22661.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3219_22661.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3219_22661.FStar_TypeChecker_Common.rank)
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
                    (let uu___3254_22811 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3254_22811.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3254_22811.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3254_22811.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3254_22811.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3254_22811.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3254_22811.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3254_22811.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3254_22811.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3254_22811.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22812,FStar_Syntax_Syntax.Tm_refine uu____22813) ->
                  let t11 =
                    let uu____22821 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22821  in
                  solve_t env
                    (let uu___3261_22847 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3261_22847.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3261_22847.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3261_22847.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3261_22847.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3261_22847.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3261_22847.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3261_22847.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3261_22847.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3261_22847.FStar_TypeChecker_Common.rank)
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
                                  (let uu___3360_23912 = wl3  in
                                   {
                                     attempting =
                                       (uu___3360_23912.attempting);
                                     wl_deferred =
                                       (uu___3360_23912.wl_deferred);
                                     ctr = (uu___3360_23912.ctr);
                                     defer_ok = (uu___3360_23912.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3360_23912.umax_heuristic_ok);
                                     tcenv = (uu___3360_23912.tcenv);
                                     wl_implicits =
                                       (uu___3360_23912.wl_implicits)
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
               mklstr
                 (fun uu____26551  ->
                    let uu____26552 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26554 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26552 uu____26554)
                in
             giveup env uu____26544 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26576 =
                  mklstr
                    (fun uu____26583  ->
                       let uu____26584 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26586 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26584 uu____26586)
                   in
                giveup env uu____26576 orig)
             else
               (let uu____26591 =
                  FStar_List.fold_left2
                    (fun uu____26612  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26612 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26633 =
                                 let uu____26638 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26639 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26638
                                   FStar_TypeChecker_Common.EQ uu____26639
                                   "effect universes"
                                  in
                               (match uu____26633 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26591 with
                | (univ_sub_probs,wl1) ->
                    let uu____26659 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26659 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26667 =
                           FStar_List.fold_right2
                             (fun uu____26704  ->
                                fun uu____26705  ->
                                  fun uu____26706  ->
                                    match (uu____26704, uu____26705,
                                            uu____26706)
                                    with
                                    | ((a1,uu____26750),(a2,uu____26752),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26785 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26785 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26667 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26812 =
                                  let uu____26815 =
                                    let uu____26818 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26818
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26815
                                   in
                                FStar_List.append univ_sub_probs uu____26812
                                 in
                              let guard =
                                let guard =
                                  let uu____26840 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26840  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3512_26849 = wl3  in
                                {
                                  attempting = (uu___3512_26849.attempting);
                                  wl_deferred = (uu___3512_26849.wl_deferred);
                                  ctr = (uu___3512_26849.ctr);
                                  defer_ok = (uu___3512_26849.defer_ok);
                                  smt_ok = (uu___3512_26849.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3512_26849.umax_heuristic_ok);
                                  tcenv = (uu___3512_26849.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26851 = attempt sub_probs wl5  in
                              solve env uu____26851))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26869 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26869
           then
             let uu____26874 =
               let uu____26876 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26876
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26878 =
               let uu____26880 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26880
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26874 uu____26878
           else ());
          (let uu____26885 =
             let uu____26890 =
               let uu____26895 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26895
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26890
               (fun uu____26912  ->
                  match uu____26912 with
                  | (c,g) ->
                      let uu____26923 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26923, g))
              in
           match uu____26885 with
           | (c12,g_lift) ->
               ((let uu____26927 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26927
                 then
                   let uu____26932 =
                     let uu____26934 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26934
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26936 =
                     let uu____26938 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26938
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26932 uu____26936
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3532_26948 = wl  in
                     {
                       attempting = (uu___3532_26948.attempting);
                       wl_deferred = (uu___3532_26948.wl_deferred);
                       ctr = (uu___3532_26948.ctr);
                       defer_ok = (uu___3532_26948.defer_ok);
                       smt_ok = (uu___3532_26948.smt_ok);
                       umax_heuristic_ok =
                         (uu___3532_26948.umax_heuristic_ok);
                       tcenv = (uu___3532_26948.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26949 =
                     let rec is_uvar t =
                       let uu____26963 =
                         let uu____26964 = FStar_Syntax_Subst.compress t  in
                         uu____26964.FStar_Syntax_Syntax.n  in
                       match uu____26963 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26968 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____26983) ->
                           is_uvar t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____26989) ->
                           is_uvar t1
                       | uu____27014 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27048  ->
                          fun uu____27049  ->
                            fun uu____27050  ->
                              match (uu____27048, uu____27049, uu____27050)
                              with
                              | ((a1,uu____27094),(a2,uu____27096),(is_sub_probs,wl2))
                                  ->
                                  let uu____27129 = is_uvar a1  in
                                  if uu____27129
                                  then
                                    ((let uu____27139 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27139
                                      then
                                        let uu____27144 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27146 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27144 uu____27146
                                      else ());
                                     (let uu____27151 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27151 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26949 with
                   | (is_sub_probs,wl2) ->
                       let uu____27179 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27179 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27187 =
                              let uu____27192 =
                                let uu____27193 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27193
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27192
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27187 with
                             | (uu____27200,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27211 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27213 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27211 s uu____27213
                                    in
                                 let uu____27216 =
                                   let uu____27245 =
                                     let uu____27246 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27246.FStar_Syntax_Syntax.n  in
                                   match uu____27245 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27306 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27306 with
                                        | (bs',c3) ->
                                            let a = FStar_List.hd bs'  in
                                            let bs1 = FStar_List.tail bs'  in
                                            let uu____27369 =
                                              let uu____27388 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27388
                                                (fun uu____27492  ->
                                                   match uu____27492 with
                                                   | (l1,l2) ->
                                                       let uu____27565 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27565))
                                               in
                                            (match uu____27369 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27670 ->
                                       let uu____27671 =
                                         let uu____27677 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27677)
                                          in
                                       FStar_Errors.raise_error uu____27671 r
                                    in
                                 (match uu____27216 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27753 =
                                        let uu____27760 =
                                          let uu____27761 =
                                            let uu____27762 =
                                              let uu____27769 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27769,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27762
                                             in
                                          [uu____27761]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27760
                                          (fun b  ->
                                             let uu____27785 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27787 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27789 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27785 uu____27787
                                               uu____27789) r
                                         in
                                      (match uu____27753 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27799 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27799
                                             then
                                               let uu____27804 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27813 =
                                                          let uu____27815 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27815
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27813) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27804
                                             else ());
                                            (let wl4 =
                                               let uu___3604_27823 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3604_27823.attempting);
                                                 wl_deferred =
                                                   (uu___3604_27823.wl_deferred);
                                                 ctr = (uu___3604_27823.ctr);
                                                 defer_ok =
                                                   (uu___3604_27823.defer_ok);
                                                 smt_ok =
                                                   (uu___3604_27823.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3604_27823.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3604_27823.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27848 =
                                                        let uu____27855 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27855, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27848) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27872 =
                                               let f_sort_is =
                                                 let uu____27882 =
                                                   let uu____27883 =
                                                     let uu____27886 =
                                                       let uu____27887 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27887.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27886
                                                      in
                                                   uu____27883.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27882 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27898,uu____27899::is)
                                                     ->
                                                     let uu____27941 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____27941
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____27974 ->
                                                     let uu____27975 =
                                                       let uu____27981 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____27981)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____27975 r
                                                  in
                                               let uu____27987 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28022  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28022
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28043 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28043
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____27987
                                                in
                                             match uu____27872 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28068 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28068
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28069 =
                                                   let g_sort_is =
                                                     let uu____28079 =
                                                       let uu____28080 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28080.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28079 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28085,uu____28086::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28146 ->
                                                         let uu____28147 =
                                                           let uu____28153 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28153)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28147 r
                                                      in
                                                   let uu____28159 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28194  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28194
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28215
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28215
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28159
                                                    in
                                                 (match uu____28069 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28242 =
                                                          let uu____28247 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28248 =
                                                            let uu____28249 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28249
                                                             in
                                                          (uu____28247,
                                                            uu____28248)
                                                           in
                                                        match uu____28242
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28277 =
                                                          let uu____28280 =
                                                            let uu____28283 =
                                                              let uu____28286
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28286
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28283
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28280
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28277
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28310 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28310
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
                                                        let uu____28321 =
                                                          let uu____28324 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun uu____28327 
                                                               ->
                                                               FStar_Pervasives_Native.Some
                                                                 uu____28327)
                                                            uu____28324
                                                           in
                                                        solve_prob orig
                                                          uu____28321 [] wl6
                                                         in
                                                      let uu____28328 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28328))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28351 =
            let univs =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28353 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28353]
              | x -> x  in
            let c12 =
              let uu___3670_28356 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3670_28356.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3670_28356.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3670_28356.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3670_28356.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28357 =
              let uu____28362 =
                FStar_All.pipe_right
                  (let uu___3673_28364 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3673_28364.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3673_28364.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3673_28364.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3673_28364.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28362
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28357
              (fun uu____28378  ->
                 match uu____28378 with
                 | (c,g) ->
                     let uu____28385 =
                       let uu____28387 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28387  in
                     if uu____28385
                     then
                       let uu____28390 =
                         let uu____28396 =
                           let uu____28398 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28400 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28398 uu____28400
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28396)
                          in
                       FStar_Errors.raise_error uu____28390 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28406 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28406
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28412 = lift_c1 ()  in
               solve_eq uu____28412 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28421  ->
                         match uu___31_28421 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28426 -> false))
                  in
               let uu____28428 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28458)::uu____28459,(wp2,uu____28461)::uu____28462)
                     -> (wp1, wp2)
                 | uu____28535 ->
                     let uu____28560 =
                       let uu____28566 =
                         let uu____28568 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28570 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28568 uu____28570
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28566)
                        in
                     FStar_Errors.raise_error uu____28560
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28428 with
               | (wpc1,wpc2) ->
                   let uu____28580 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28580
                   then
                     let uu____28583 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28583 wl
                   else
                     (let uu____28587 =
                        let uu____28594 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28594  in
                      match uu____28587 with
                      | (c2_decl,qualifiers) ->
                          let uu____28615 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28615
                          then
                            let c1_repr =
                              let uu____28622 =
                                let uu____28623 =
                                  let uu____28624 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28624  in
                                let uu____28625 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28623 uu____28625
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28622
                               in
                            let c2_repr =
                              let uu____28628 =
                                let uu____28629 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28630 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28629 uu____28630
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28628
                               in
                            let uu____28632 =
                              let uu____28637 =
                                let uu____28639 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28641 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28639
                                  uu____28641
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28637
                               in
                            (match uu____28632 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28647 = attempt [prob] wl2  in
                                 solve env uu____28647)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28667 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28667
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28690 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28690
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
                                        let uu____28700 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28700 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28707 =
                                        let uu____28714 =
                                          let uu____28715 =
                                            let uu____28732 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28735 =
                                              let uu____28746 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28746; wpc1_2]  in
                                            (uu____28732, uu____28735)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28715
                                           in
                                        FStar_Syntax_Syntax.mk uu____28714
                                         in
                                      uu____28707
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
                                     let uu____28795 =
                                       let uu____28802 =
                                         let uu____28803 =
                                           let uu____28820 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28823 =
                                             let uu____28834 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28843 =
                                               let uu____28854 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28854; wpc1_2]  in
                                             uu____28834 :: uu____28843  in
                                           (uu____28820, uu____28823)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28803
                                          in
                                       FStar_Syntax_Syntax.mk uu____28802  in
                                     uu____28795 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28908 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28908
                              then
                                let uu____28913 =
                                  let uu____28915 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28915
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28913
                              else ());
                             (let uu____28919 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28919 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28928 =
                                      let uu____28931 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun uu____28934  ->
                                           FStar_Pervasives_Native.Some
                                             uu____28934) uu____28931
                                       in
                                    solve_prob orig uu____28928 [] wl1  in
                                  let uu____28935 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28935))))
           in
        let uu____28936 = FStar_Util.physical_equality c1 c2  in
        if uu____28936
        then
          let uu____28939 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28939
        else
          ((let uu____28943 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28943
            then
              let uu____28948 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28950 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28948
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28950
            else ());
           (let uu____28955 =
              let uu____28964 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28967 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28964, uu____28967)  in
            match uu____28955 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28985),FStar_Syntax_Syntax.Total
                    (t2,uu____28987)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29004 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29004 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29006,FStar_Syntax_Syntax.Total uu____29007) ->
                     let uu____29024 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29024 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29028),FStar_Syntax_Syntax.Total
                    (t2,uu____29030)) ->
                     let uu____29047 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29047 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29050),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29052)) ->
                     let uu____29069 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29069 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29072),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29074)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29091 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29091 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29094),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29096)) ->
                     let uu____29113 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29113 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29116,FStar_Syntax_Syntax.Comp uu____29117) ->
                     let uu____29126 =
                       let uu___3797_29129 = problem  in
                       let uu____29132 =
                         let uu____29133 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29133
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3797_29129.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29132;
                         FStar_TypeChecker_Common.relation =
                           (uu___3797_29129.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3797_29129.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3797_29129.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3797_29129.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3797_29129.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3797_29129.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3797_29129.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3797_29129.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29126 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29134,FStar_Syntax_Syntax.Comp uu____29135) ->
                     let uu____29144 =
                       let uu___3797_29147 = problem  in
                       let uu____29150 =
                         let uu____29151 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29151
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3797_29147.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29150;
                         FStar_TypeChecker_Common.relation =
                           (uu___3797_29147.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3797_29147.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3797_29147.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3797_29147.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3797_29147.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3797_29147.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3797_29147.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3797_29147.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29144 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29152,FStar_Syntax_Syntax.GTotal uu____29153) ->
                     let uu____29162 =
                       let uu___3809_29165 = problem  in
                       let uu____29168 =
                         let uu____29169 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29169
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3809_29165.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3809_29165.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3809_29165.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29168;
                         FStar_TypeChecker_Common.element =
                           (uu___3809_29165.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3809_29165.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3809_29165.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3809_29165.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3809_29165.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3809_29165.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29162 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29170,FStar_Syntax_Syntax.Total uu____29171) ->
                     let uu____29180 =
                       let uu___3809_29183 = problem  in
                       let uu____29186 =
                         let uu____29187 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29187
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3809_29183.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3809_29183.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3809_29183.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29186;
                         FStar_TypeChecker_Common.element =
                           (uu___3809_29183.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3809_29183.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3809_29183.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3809_29183.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3809_29183.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3809_29183.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29180 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29188,FStar_Syntax_Syntax.Comp uu____29189) ->
                     let uu____29190 =
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
                     if uu____29190
                     then
                       let uu____29193 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29193 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29200 =
                            let uu____29205 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29205
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29214 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29215 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29214, uu____29215))
                             in
                          match uu____29200 with
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
                           (let uu____29223 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29223
                            then
                              let uu____29228 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name
                                 in
                              let uu____29230 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____29228 uu____29230
                            else ());
                           (let uu____29235 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29235 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29238 =
                                  mklstr
                                    (fun uu____29245  ->
                                       let uu____29246 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29248 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29246 uu____29248)
                                   in
                                giveup env uu____29238 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29259 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29259 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29309 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29309 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29334 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29365  ->
                match uu____29365 with
                | (u1,u2) ->
                    let uu____29373 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29375 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29373 uu____29375))
         in
      FStar_All.pipe_right uu____29334 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29412,[])) when
          let uu____29439 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29439 -> "{}"
      | uu____29442 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29469 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29469
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29481 =
              FStar_List.map
                (fun uu____29494  ->
                   match uu____29494 with
                   | (uu____29501,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29481 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29512 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29512 imps
  
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
                  let uu____29569 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29569
                  then
                    let uu____29577 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29579 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29577
                      (rel_to_string rel) uu____29579
                  else "TOP"  in
                let uu____29585 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29585 with
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
              let uu____29645 =
                let uu____29648 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun uu____29651  ->
                     FStar_Pervasives_Native.Some uu____29651) uu____29648
                 in
              FStar_Syntax_Syntax.new_bv uu____29645 t1  in
            let uu____29652 =
              let uu____29657 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29657
               in
            match uu____29652 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29715 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29715
         then
           let uu____29720 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29720
         else ());
        (let uu____29727 =
           FStar_Util.record_time (fun uu____29734  -> solve env probs)  in
         match uu____29727 with
         | (sol,ms) ->
             ((let uu____29746 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29746
               then
                 let uu____29751 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29751
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29764 =
                     FStar_Util.record_time
                       (fun uu____29771  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29764 with
                    | ((),ms1) ->
                        ((let uu____29782 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29782
                          then
                            let uu____29787 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29787
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29799 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29799
                     then
                       let uu____29806 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29806
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
          ((let uu____29832 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29832
            then
              let uu____29837 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29837
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29845 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29845
             then
               let uu____29850 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29850
             else ());
            (let f2 =
               let uu____29856 =
                 let uu____29857 = FStar_Syntax_Util.unmeta f1  in
                 uu____29857.FStar_Syntax_Syntax.n  in
               match uu____29856 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29861 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3926_29862 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3926_29862.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3926_29862.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3926_29862.FStar_TypeChecker_Common.implicits)
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
            let uu____29905 =
              let uu____29906 =
                let uu____29907 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____29908  ->
                       FStar_TypeChecker_Common.NonTrivial uu____29908)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29907;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29906  in
            FStar_All.pipe_left
              (fun uu____29915  -> FStar_Pervasives_Native.Some uu____29915)
              uu____29905
  
let with_guard_no_simp :
  'uuuuuu29925 .
    'uuuuuu29925 ->
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
            let uu____29965 =
              let uu____29966 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____29967  ->
                     FStar_TypeChecker_Common.NonTrivial uu____29967)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29966;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____29965
  
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
          (let uu____30000 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30000
           then
             let uu____30005 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30007 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30005
               uu____30007
           else ());
          (let uu____30012 =
             let uu____30017 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30017
              in
           match uu____30012 with
           | (prob,wl) ->
               let g =
                 let uu____30025 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30033  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30025  in
               ((let uu____30051 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30051
                 then
                   let uu____30056 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30056
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
        let uu____30077 = try_teq true env t1 t2  in
        match uu____30077 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30082 = FStar_TypeChecker_Env.get_range env  in
              let uu____30083 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30082 uu____30083);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30091 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30091
              then
                let uu____30096 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30098 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30100 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30096
                  uu____30098 uu____30100
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
        (let uu____30124 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30124
         then
           let uu____30129 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30131 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30129
             uu____30131
         else ());
        (let uu____30136 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30136 with
         | (prob,x,wl) ->
             let g =
               let uu____30151 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30160  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30151  in
             ((let uu____30178 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30178
               then
                 let uu____30183 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30183
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30191 =
                     let uu____30192 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30192 g1  in
                   FStar_Pervasives_Native.Some uu____30191)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30214 = FStar_TypeChecker_Env.get_range env  in
          let uu____30215 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30214 uu____30215
  
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
        (let uu____30244 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30244
         then
           let uu____30249 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30251 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30249 uu____30251
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30262 =
           let uu____30269 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30269 "sub_comp"
            in
         match uu____30262 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30282 =
                 FStar_Util.record_time
                   (fun uu____30294  ->
                      let uu____30295 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30304  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30295)
                  in
               match uu____30282 with
               | (r,ms) ->
                   ((let uu____30332 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30332
                     then
                       let uu____30337 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30339 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30341 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30337 uu____30339
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30341
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
      fun uu____30379  ->
        match uu____30379 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30422 =
                 let uu____30428 =
                   let uu____30430 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30432 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30430 uu____30432
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30428)  in
               let uu____30436 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30422 uu____30436)
               in
            let equiv v v' =
              let uu____30449 =
                let uu____30454 = FStar_Syntax_Subst.compress_univ v  in
                let uu____30455 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30454, uu____30455)  in
              match uu____30449 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30475 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v  ->
                      let uu____30506 = FStar_Syntax_Subst.compress_univ v
                         in
                      match uu____30506 with
                      | FStar_Syntax_Syntax.U_unif uu____30513 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30542  ->
                                    match uu____30542 with
                                    | (u,v') ->
                                        let uu____30551 = equiv v v'  in
                                        if uu____30551
                                        then
                                          let uu____30556 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____30556 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v)]
                      | uu____30577 -> []))
               in
            let uu____30582 =
              let wl =
                let uu___4037_30586 = empty_worklist env  in
                {
                  attempting = (uu___4037_30586.attempting);
                  wl_deferred = (uu___4037_30586.wl_deferred);
                  ctr = (uu___4037_30586.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4037_30586.smt_ok);
                  umax_heuristic_ok = (uu___4037_30586.umax_heuristic_ok);
                  tcenv = (uu___4037_30586.tcenv);
                  wl_implicits = (uu___4037_30586.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30605  ->
                      match uu____30605 with
                      | (lb,v) ->
                          let uu____30612 =
                            solve_universe_eq (~- Prims.int_one) wl lb v  in
                          (match uu____30612 with
                           | USolved wl1 -> ()
                           | uu____30615 -> fail lb v)))
               in
            let rec check_ineq uu____30626 =
              match uu____30626 with
              | (u,v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v  in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30638) -> true
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
                      uu____30662,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30664,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30675) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v1)))
                   | (uu____30683,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v2  -> check_ineq (u1, v2)))
                   | uu____30692 -> false)
               in
            let uu____30698 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30715  ->
                      match uu____30715 with
                      | (u,v) ->
                          let uu____30723 = check_ineq (u, v)  in
                          if uu____30723
                          then true
                          else
                            ((let uu____30731 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30731
                              then
                                let uu____30736 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30738 =
                                  FStar_Syntax_Print.univ_to_string v  in
                                FStar_Util.print2 "%s </= %s" uu____30736
                                  uu____30738
                              else ());
                             false)))
               in
            if uu____30698
            then ()
            else
              ((let uu____30748 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30748
                then
                  ((let uu____30754 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30754);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30766 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30766))
                else ());
               (let uu____30779 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30779))
  
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
        let fail uu____30852 =
          match uu____30852 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4114_30875 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4114_30875.attempting);
            wl_deferred = (uu___4114_30875.wl_deferred);
            ctr = (uu___4114_30875.ctr);
            defer_ok;
            smt_ok = (uu___4114_30875.smt_ok);
            umax_heuristic_ok = (uu___4114_30875.umax_heuristic_ok);
            tcenv = (uu___4114_30875.tcenv);
            wl_implicits = (uu___4114_30875.wl_implicits)
          }  in
        (let uu____30878 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30878
         then
           let uu____30883 = FStar_Util.string_of_bool defer_ok  in
           let uu____30885 = wl_to_string wl  in
           let uu____30887 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30883 uu____30885 uu____30887
         else ());
        (let g1 =
           let uu____30893 = solve_and_commit env wl fail  in
           match uu____30893 with
           | FStar_Pervasives_Native.Some
               (uu____30900::uu____30901,uu____30902) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4129_30931 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4129_30931.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4129_30931.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30932 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4134_30941 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4134_30941.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4134_30941.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4134_30941.FStar_TypeChecker_Common.implicits)
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
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___4146_31018 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4146_31018.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4146_31018.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4146_31018.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____31019 =
            let uu____31021 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____31021  in
          if uu____31019
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug
                  then
                    (let uu____31033 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____31034 =
                       let uu____31036 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____31036
                        in
                     FStar_Errors.diag uu____31033 uu____31034)
                  else ();
                  (let vc1 =
                     let uu____31042 =
                       let uu____31046 =
                         let uu____31048 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____31048  in
                       FStar_Pervasives_Native.Some uu____31046  in
                     FStar_Profiling.profile
                       (fun uu____31051  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____31042 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug
                   then
                     (let uu____31055 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31056 =
                        let uu____31058 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31058
                         in
                      FStar_Errors.diag uu____31055 uu____31056)
                   else ();
                   (let uu____31064 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31064
                      "discharge_guard'" env vc1);
                   (let uu____31066 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31066 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug
                           then
                             (let uu____31075 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31076 =
                                let uu____31078 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31078
                                 in
                              FStar_Errors.diag uu____31075 uu____31076)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug
                           then
                             (let uu____31088 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31089 =
                                let uu____31091 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31091
                                 in
                              FStar_Errors.diag uu____31088 uu____31089)
                           else ();
                           (let vcs =
                              let uu____31105 = FStar_Options.use_tactics ()
                                 in
                              if uu____31105
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31127  ->
                                     (let uu____31129 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        (fun uu____31131  -> ()) uu____31129);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31174  ->
                                              match uu____31174 with
                                              | (env1,goal,opts) ->
                                                  let uu____31190 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31190, opts)))))
                              else
                                (let uu____31194 =
                                   let uu____31201 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31201)  in
                                 [uu____31194])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31234  ->
                                    match uu____31234 with
                                    | (env1,goal,opts) ->
                                        let uu____31244 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31244 with
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
                                                (let uu____31255 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31256 =
                                                   let uu____31258 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31260 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31258 uu____31260
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31255 uu____31256)
                                              else ();
                                              if debug
                                              then
                                                (let uu____31267 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31268 =
                                                   let uu____31270 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31270
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31267 uu____31268)
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
      let uu____31288 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31288 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31297 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31297
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31311 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31311 with
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
        let uu____31341 = try_teq false env t1 t2  in
        match uu____31341 with
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
            let uu____31385 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31385 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31398 ->
                     let uu____31411 =
                       let uu____31412 = FStar_Syntax_Subst.compress r  in
                       uu____31412.FStar_Syntax_Syntax.n  in
                     (match uu____31411 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31417) ->
                          unresolved ctx_u'
                      | uu____31434 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31458 = acc  in
            match uu____31458 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd::tl ->
                     let uu____31477 = hd  in
                     (match uu____31477 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl
                          else
                            (let uu____31488 = unresolved ctx_u  in
                             if uu____31488
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd :: out), changed) tl
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31512 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31512
                                     then
                                       let uu____31516 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31516
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31525 = teq_nosmt env1 t tm
                                          in
                                       match uu____31525 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4259_31535 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4259_31535.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4259_31535.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4259_31535.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4259_31535.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4259_31535.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4259_31535.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4259_31535.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd1 =
                                       let uu___4262_31543 = hd  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4262_31543.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4262_31543.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4262_31543.FStar_TypeChecker_Common.imp_range)
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
                                    let uu___4266_31554 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4266_31554.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4266_31554.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4266_31554.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4266_31554.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4266_31554.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4266_31554.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4266_31554.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4266_31554.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4266_31554.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4266_31554.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4266_31554.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4266_31554.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4266_31554.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4266_31554.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4266_31554.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4266_31554.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4266_31554.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4266_31554.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4266_31554.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4266_31554.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4266_31554.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4266_31554.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4266_31554.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4266_31554.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4266_31554.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4266_31554.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4266_31554.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4266_31554.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4266_31554.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4266_31554.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4266_31554.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4266_31554.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4266_31554.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4266_31554.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4266_31554.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4266_31554.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4266_31554.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4266_31554.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4266_31554.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4266_31554.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4266_31554.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4266_31554.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4266_31554.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4266_31554.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4266_31554.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4266_31554.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4271_31559 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4271_31559.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4271_31559.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4271_31559.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4271_31559.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4271_31559.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4271_31559.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4271_31559.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4271_31559.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4271_31559.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4271_31559.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4271_31559.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4271_31559.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4271_31559.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4271_31559.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4271_31559.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4271_31559.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4271_31559.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4271_31559.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4271_31559.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4271_31559.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4271_31559.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4271_31559.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4271_31559.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4271_31559.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4271_31559.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4271_31559.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4271_31559.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4271_31559.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4271_31559.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4271_31559.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4271_31559.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4271_31559.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4271_31559.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4271_31559.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4271_31559.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4271_31559.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4271_31559.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4271_31559.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4271_31559.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4271_31559.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4271_31559.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4271_31559.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4271_31559.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4271_31559.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4271_31559.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4271_31559.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31564 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31564
                                   then
                                     let uu____31569 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31571 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31573 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31575 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31569 uu____31571 uu____31573
                                       reason uu____31575
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4277_31582  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31589 =
                                             let uu____31599 =
                                               let uu____31607 =
                                                 let uu____31609 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31611 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31613 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31609 uu____31611
                                                   uu____31613
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31607, r)
                                                in
                                             [uu____31599]  in
                                           FStar_Errors.add_errors
                                             uu____31589);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31632 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31643  ->
                                               let uu____31644 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31646 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31648 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31644 uu____31646
                                                 reason uu____31648)) env2 g1
                                         true
                                        in
                                     match uu____31632 with
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
          let uu___4289_31656 = g  in
          let uu____31657 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4289_31656.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4289_31656.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4289_31656.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31657
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
        let uu____31697 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31697 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31698 = discharge_guard env g1  in
          FStar_All.pipe_left (fun uu____31699  -> ()) uu____31698
      | imp::uu____31701 ->
          let uu____31704 =
            let uu____31710 =
              let uu____31712 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31714 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31712 uu____31714
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31710)
             in
          FStar_Errors.raise_error uu____31704
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31734 = teq env t1 t2  in
        force_trivial_guard env uu____31734
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31753 = teq_nosmt env t1 t2  in
        match uu____31753 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4314_31772 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4314_31772.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4314_31772.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4314_31772.FStar_TypeChecker_Common.implicits)
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
        (let uu____31808 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31808
         then
           let uu____31813 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31815 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31813
             uu____31815
         else ());
        (let uu____31820 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31820 with
         | (prob,x,wl) ->
             let g =
               let uu____31839 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31848  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31839  in
             ((let uu____31866 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31866
               then
                 let uu____31871 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31873 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31875 =
                   let uu____31877 = FStar_Util.must g  in
                   guard_to_string env uu____31877  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31871 uu____31873 uu____31875
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
        let uu____31914 = check_subtyping env t1 t2  in
        match uu____31914 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31933 =
              let uu____31934 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31934 g  in
            FStar_Pervasives_Native.Some uu____31933
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31953 = check_subtyping env t1 t2  in
        match uu____31953 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31972 =
              let uu____31973 =
                let uu____31974 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31974]  in
              FStar_TypeChecker_Env.close_guard env uu____31973 g  in
            FStar_Pervasives_Native.Some uu____31972
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32012 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32012
         then
           let uu____32017 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32019 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32017
             uu____32019
         else ());
        (let uu____32024 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32024 with
         | (prob,x,wl) ->
             let g =
               let uu____32039 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32048  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32039  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32069 =
                      let uu____32070 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32070]  in
                    FStar_TypeChecker_Env.close_guard env uu____32069 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32111 = subtype_nosmt env t1 t2  in
        match uu____32111 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  