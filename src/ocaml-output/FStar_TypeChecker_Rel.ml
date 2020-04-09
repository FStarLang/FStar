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
              fun should_check1  ->
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
                        should_check1;
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
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
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
  'Auu____1094 .
    (FStar_Syntax_Syntax.term * 'Auu____1094) Prims.list -> Prims.string
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
  'Auu____1227 .
    'Auu____1227 FStar_TypeChecker_Common.problem ->
      'Auu____1227 FStar_TypeChecker_Common.problem
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
  'Auu____1247 .
    'Auu____1247 FStar_TypeChecker_Common.problem ->
      'Auu____1247 FStar_TypeChecker_Common.problem
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
          (fun _1273  -> FStar_TypeChecker_Common.TProb _1273)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1279  -> FStar_TypeChecker_Common.CProb _1279)
  
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
  'Auu____1418 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1418) Prims.list -> unit
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
  'Auu____1832 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1832 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
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
  'Auu____1937 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1937 ->
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
          (fun _2016  -> FStar_TypeChecker_Common.TProb _2016) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _2022  -> FStar_TypeChecker_Common.CProb _2022) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2030 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2030 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2050  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2092 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2092 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2092 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2092 FStar_TypeChecker_Common.problem *
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
  'Auu____2479 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2479 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2479 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2479 FStar_TypeChecker_Common.problem *
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
  'Auu____2711 .
    worklist ->
      'Auu____2711 FStar_TypeChecker_Common.problem ->
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
  'Auu____3132 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3132) ->
        (FStar_Syntax_Syntax.term * 'Auu____3132)
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
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
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
              aux norm1 uu____3468
          | FStar_Syntax_Syntax.Tm_uinst uu____3469 ->
              if norm1
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
              if norm1
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
              if norm1
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
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4174 = base_and_refinement_maybe_delta delta1 env t  in
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
  'Auu____4369 .
    ('Auu____4369 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
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
    | (head1,_args) ->
        let uu____4447 =
          let uu____4448 = FStar_Syntax_Subst.compress head1  in
          uu____4448.FStar_Syntax_Syntax.n  in
        (match uu____4447 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4452 -> true
         | uu____4466 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4474 = FStar_Syntax_Util.head_and_args t  in
    match uu____4474 with
    | (head1,_args) ->
        let uu____4517 =
          let uu____4518 = FStar_Syntax_Subst.compress head1  in
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
      | (head1,args) ->
          let uu____4611 =
            let uu____4612 = FStar_Syntax_Subst.compress head1  in
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
                     | (v1,t_v,wl1) ->
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
                          ((t1, v1, all_args), wl1))))
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
             let fail1 uu____5430 =
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
                            | uu____5549 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5559 =
                 let uu____5561 = is_flex g  in Prims.op_Negation uu____5561
                  in
               if uu____5559
               then (if resolve_ok then wl else (fail1 (); wl))
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
      let uvars1 =
        let uu____5692 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5692 FStar_Util.set_elements  in
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
      let uu____5732 = occurs uk t  in
      match uu____5732 with
      | (uvars1,occurs1) ->
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
            let uu____5895 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5895 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5946 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6003  ->
             match uu____6003 with
             | (x,uu____6015) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6033 = FStar_List.last bs  in
      match uu____6033 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6057) ->
          let uu____6068 =
            FStar_Util.prefix_until
              (fun uu___21_6083  ->
                 match uu___21_6083 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6086 -> false) g
             in
          (match uu____6068 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6100,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6137 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6137 with
        | (pfx,uu____6147) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6159 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6159 with
             | (uu____6167,src',wl1) ->
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
                 | uu____6281 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6282 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6346  ->
                  fun uu____6347  ->
                    match (uu____6346, uu____6347) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6450 =
                          let uu____6452 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6452
                           in
                        if uu____6450
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6486 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6486
                           then
                             let uu____6503 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6503)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6282 with | (isect,uu____6553) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6589 'Auu____6590 .
    (FStar_Syntax_Syntax.bv * 'Auu____6589) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6590) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6648  ->
              fun uu____6649  ->
                match (uu____6648, uu____6649) with
                | ((a,uu____6668),(b,uu____6670)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6686 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6686) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6717  ->
           match uu____6717 with
           | (y,uu____6724) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6734 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6734) Prims.list ->
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
                   let uu____6896 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6896
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6929 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6981 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7025 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7046 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7054  ->
    match uu___22_7054 with
    | MisMatch (d1,d2) ->
        let uu____7066 =
          let uu____7068 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7070 =
            let uu____7072 =
              let uu____7074 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7074 ")"  in
            Prims.op_Hat ") (" uu____7072  in
          Prims.op_Hat uu____7068 uu____7070  in
        Prims.op_Hat "MisMatch (" uu____7066
    | HeadMatch u ->
        let uu____7081 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7081
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7090  ->
    match uu___23_7090 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7107 -> HeadMatch false
  
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
          let uu____7129 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7129 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7140 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7164 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7174 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7193 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7193
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7194 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7195 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7196 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7209 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7223 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7247) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7253,uu____7254) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7296) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7321;
             FStar_Syntax_Syntax.index = uu____7322;
             FStar_Syntax_Syntax.sort = t2;_},uu____7324)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7332 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7333 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7334 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7349 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7356 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7376 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7376
  
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
           { FStar_Syntax_Syntax.blob = uu____7395;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7396;
             FStar_Syntax_Syntax.ltyp = uu____7397;
             FStar_Syntax_Syntax.rng = uu____7398;_},uu____7399)
            ->
            let uu____7410 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7410 t21
        | (uu____7411,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7412;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7413;
             FStar_Syntax_Syntax.ltyp = uu____7414;
             FStar_Syntax_Syntax.rng = uu____7415;_})
            ->
            let uu____7426 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7426
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7438 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7438
            then FullMatch
            else
              (let uu____7443 =
                 let uu____7452 =
                   let uu____7455 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7455  in
                 let uu____7456 =
                   let uu____7459 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7459  in
                 (uu____7452, uu____7456)  in
               MisMatch uu____7443)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7465),FStar_Syntax_Syntax.Tm_uinst (g,uu____7467)) ->
            let uu____7476 = head_matches env f g  in
            FStar_All.pipe_right uu____7476 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7477) -> HeadMatch true
        | (uu____7479,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7483 = FStar_Const.eq_const c d  in
            if uu____7483
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7493),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7495)) ->
            let uu____7528 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7528
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7538),FStar_Syntax_Syntax.Tm_refine (y,uu____7540)) ->
            let uu____7549 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7549 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7551),uu____7552) ->
            let uu____7557 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7557 head_match
        | (uu____7558,FStar_Syntax_Syntax.Tm_refine (x,uu____7560)) ->
            let uu____7565 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7565 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7566,FStar_Syntax_Syntax.Tm_type
           uu____7567) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7569,FStar_Syntax_Syntax.Tm_arrow uu____7570) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7601),FStar_Syntax_Syntax.Tm_app (head',uu____7603))
            ->
            let uu____7652 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7652 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7654),uu____7655) ->
            let uu____7680 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7680 head_match
        | (uu____7681,FStar_Syntax_Syntax.Tm_app (head1,uu____7683)) ->
            let uu____7708 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7708 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7709,FStar_Syntax_Syntax.Tm_let
           uu____7710) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7738,FStar_Syntax_Syntax.Tm_match uu____7739) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7785,FStar_Syntax_Syntax.Tm_abs
           uu____7786) -> HeadMatch true
        | uu____7824 ->
            let uu____7829 =
              let uu____7838 = delta_depth_of_term env t11  in
              let uu____7841 = delta_depth_of_term env t21  in
              (uu____7838, uu____7841)  in
            MisMatch uu____7829
  
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
              let uu____7910 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7910  in
            (let uu____7912 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7912
             then
               let uu____7917 = FStar_Syntax_Print.term_to_string t  in
               let uu____7919 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7917 uu____7919
             else ());
            (let uu____7924 =
               let uu____7925 = FStar_Syntax_Util.un_uinst head1  in
               uu____7925.FStar_Syntax_Syntax.n  in
             match uu____7924 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7931 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7931 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7945 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7945
                        then
                          let uu____7950 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7950
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7955 ->
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
                      let uu____7973 =
                        let uu____7975 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7975 = FStar_Syntax_Util.Equal  in
                      if uu____7973
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7982 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7982
                          then
                            let uu____7987 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____7989 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7987
                              uu____7989
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7994 -> FStar_Pervasives_Native.None)
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
            (let uu____8146 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8146
             then
               let uu____8151 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8153 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8155 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8151
                 uu____8153 uu____8155
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8183 =
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
               match uu____8183 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8231 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8231 with
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
                  uu____8269),uu____8270)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8291 =
                      let uu____8300 = maybe_inline t11  in
                      let uu____8303 = maybe_inline t21  in
                      (uu____8300, uu____8303)  in
                    match uu____8291 with
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
                 (uu____8346,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8347))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8368 =
                      let uu____8377 = maybe_inline t11  in
                      let uu____8380 = maybe_inline t21  in
                      (uu____8377, uu____8380)  in
                    match uu____8368 with
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
             | MisMatch uu____8435 -> fail1 n_delta r t11 t21
             | uu____8444 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8459 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8459
           then
             let uu____8464 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8466 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8468 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8476 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8493 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8493
                    (fun uu____8528  ->
                       match uu____8528 with
                       | (t11,t21) ->
                           let uu____8536 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8538 =
                             let uu____8540 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8540  in
                           Prims.op_Hat uu____8536 uu____8538))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8464 uu____8466 uu____8468 uu____8476
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8557 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8557 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8572  ->
    match uu___24_8572 with
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
      let uu___1215_8621 = p  in
      let uu____8624 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8625 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1215_8621.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8624;
        FStar_TypeChecker_Common.relation =
          (uu___1215_8621.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8625;
        FStar_TypeChecker_Common.element =
          (uu___1215_8621.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1215_8621.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1215_8621.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1215_8621.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1215_8621.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1215_8621.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8640 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8640
            (fun _8645  -> FStar_TypeChecker_Common.TProb _8645)
      | FStar_TypeChecker_Common.CProb uu____8646 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8669 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8669 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8677 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8677 with
           | (lh,lhs_args) ->
               let uu____8724 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8724 with
                | (rh,rhs_args) ->
                    let uu____8771 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8784,FStar_Syntax_Syntax.Tm_uvar uu____8785)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8874 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8901,uu____8902)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8917,FStar_Syntax_Syntax.Tm_uvar uu____8918)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8933,FStar_Syntax_Syntax.Tm_arrow uu____8934)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1266_8964 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1266_8964.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1266_8964.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1266_8964.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1266_8964.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1266_8964.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1266_8964.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1266_8964.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1266_8964.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1266_8964.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8967,FStar_Syntax_Syntax.Tm_type uu____8968)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1266_8984 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1266_8984.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1266_8984.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1266_8984.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1266_8984.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1266_8984.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1266_8984.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1266_8984.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1266_8984.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1266_8984.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8987,FStar_Syntax_Syntax.Tm_uvar uu____8988)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1266_9004 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1266_9004.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1266_9004.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1266_9004.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1266_9004.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1266_9004.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1266_9004.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1266_9004.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1266_9004.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1266_9004.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9007,FStar_Syntax_Syntax.Tm_uvar uu____9008)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9023,uu____9024)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9039,FStar_Syntax_Syntax.Tm_uvar uu____9040)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9055,uu____9056) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8771 with
                     | (rank,tp1) ->
                         let uu____9069 =
                           FStar_All.pipe_right
                             (let uu___1286_9073 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1286_9073.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1286_9073.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1286_9073.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1286_9073.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1286_9073.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1286_9073.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1286_9073.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1286_9073.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1286_9073.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9076  ->
                                FStar_TypeChecker_Common.TProb _9076)
                            in
                         (rank, uu____9069))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9080 =
            FStar_All.pipe_right
              (let uu___1290_9084 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1290_9084.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1290_9084.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1290_9084.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1290_9084.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1290_9084.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1290_9084.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1290_9084.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1290_9084.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1290_9084.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9087  -> FStar_TypeChecker_Common.CProb _9087)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9080)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9147 probs =
      match uu____9147 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9228 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9249 = rank wl.tcenv hd1  in
               (match uu____9249 with
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
                      (let uu____9310 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9315 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9315)
                          in
                       if uu____9310
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
          let uu____9388 = FStar_Syntax_Util.head_and_args t  in
          match uu____9388 with
          | (hd1,uu____9407) ->
              let uu____9432 =
                let uu____9433 = FStar_Syntax_Subst.compress hd1  in
                uu____9433.FStar_Syntax_Syntax.n  in
              (match uu____9432 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9438) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9473  ->
                           match uu____9473 with
                           | (y,uu____9482) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9505  ->
                                       match uu____9505 with
                                       | (x,uu____9514) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9519 -> false)
           in
        let uu____9521 = rank tcenv p  in
        match uu____9521 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9530 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9611 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9630 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9649 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9666 = FStar_Thunk.mkv s  in UFailed uu____9666 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9681 = mklstr s  in UFailed uu____9681 
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
                        let uu____9732 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9732 with
                        | (k,uu____9740) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9753 -> false)))
            | uu____9755 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9807 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9815 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9815 = Prims.int_zero))
                           in
                        if uu____9807 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9836 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9844 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9844 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9836)
               in
            let uu____9848 = filter1 u12  in
            let uu____9851 = filter1 u22  in (uu____9848, uu____9851)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9886 = filter_out_common_univs us1 us2  in
                   (match uu____9886 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9946 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9946 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9949 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9966  ->
                               let uu____9967 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____9969 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9967 uu____9969))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9995 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9995 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10021 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10021 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10024 ->
                   ufailed_thunk
                     (fun uu____10035  ->
                        let uu____10036 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10038 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10036 uu____10038 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10041,uu____10042) ->
              let uu____10044 =
                let uu____10046 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10048 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10046 uu____10048
                 in
              failwith uu____10044
          | (FStar_Syntax_Syntax.U_unknown ,uu____10051) ->
              let uu____10052 =
                let uu____10054 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10056 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10054 uu____10056
                 in
              failwith uu____10052
          | (uu____10059,FStar_Syntax_Syntax.U_bvar uu____10060) ->
              let uu____10062 =
                let uu____10064 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10066 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10064 uu____10066
                 in
              failwith uu____10062
          | (uu____10069,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10070 =
                let uu____10072 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10074 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10072 uu____10074
                 in
              failwith uu____10070
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10104 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10104
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10121 = occurs_univ v1 u3  in
              if uu____10121
              then
                let uu____10124 =
                  let uu____10126 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10128 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10126 uu____10128
                   in
                try_umax_components u11 u21 uu____10124
              else
                (let uu____10133 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10133)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10145 = occurs_univ v1 u3  in
              if uu____10145
              then
                let uu____10148 =
                  let uu____10150 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10152 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10150 uu____10152
                   in
                try_umax_components u11 u21 uu____10148
              else
                (let uu____10157 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10157)
          | (FStar_Syntax_Syntax.U_max uu____10158,uu____10159) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10167 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10167
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10173,FStar_Syntax_Syntax.U_max uu____10174) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10182 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10182
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10188,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10190,FStar_Syntax_Syntax.U_name uu____10191) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10193) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10195) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10197,FStar_Syntax_Syntax.U_succ uu____10198) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10200,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10307 = bc1  in
      match uu____10307 with
      | (bs1,mk_cod1) ->
          let uu____10351 = bc2  in
          (match uu____10351 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10462 = aux xs ys  in
                     (match uu____10462 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10545 =
                       let uu____10552 = mk_cod1 xs  in ([], uu____10552)  in
                     let uu____10555 =
                       let uu____10562 = mk_cod2 ys  in ([], uu____10562)  in
                     (uu____10545, uu____10555)
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
                  let uu____10631 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10631 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10634 =
                    let uu____10635 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10635 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10634
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10640 = has_type_guard t1 t2  in (uu____10640, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10641 = has_type_guard t2 t1  in (uu____10641, wl)
  
let is_flex_pat :
  'Auu____10651 'Auu____10652 'Auu____10653 .
    ('Auu____10651 * 'Auu____10652 * 'Auu____10653 Prims.list) -> Prims.bool
  =
  fun uu___25_10667  ->
    match uu___25_10667 with
    | (uu____10676,uu____10677,[]) -> true
    | uu____10681 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10714 = f  in
      match uu____10714 with
      | (uu____10721,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10722;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10723;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10726;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10727;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10728;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10729;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10799  ->
                 match uu____10799 with
                 | (y,uu____10808) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10962 =
                  let uu____10977 =
                    let uu____10980 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10980  in
                  ((FStar_List.rev pat_binders), uu____10977)  in
                FStar_Pervasives_Native.Some uu____10962
            | (uu____11013,[]) ->
                let uu____11044 =
                  let uu____11059 =
                    let uu____11062 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11062  in
                  ((FStar_List.rev pat_binders), uu____11059)  in
                FStar_Pervasives_Native.Some uu____11044
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11153 =
                  let uu____11154 = FStar_Syntax_Subst.compress a  in
                  uu____11154.FStar_Syntax_Syntax.n  in
                (match uu____11153 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11174 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11174
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1618_11204 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1618_11204.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1618_11204.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11208 =
                            let uu____11209 =
                              let uu____11216 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11216)  in
                            FStar_Syntax_Syntax.NT uu____11209  in
                          [uu____11208]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1624_11232 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1624_11232.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1624_11232.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11233 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11273 =
                  let uu____11280 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11280  in
                (match uu____11273 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11339 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11364 ->
               let uu____11365 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11365 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11661 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11661
       then
         let uu____11666 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11666
       else ());
      (let uu____11672 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____11672
       then
         let uu____11677 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11677
       else ());
      (let uu____11682 = next_prob probs  in
       match uu____11682 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1651_11709 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1651_11709.wl_deferred);
               ctr = (uu___1651_11709.ctr);
               defer_ok = (uu___1651_11709.defer_ok);
               smt_ok = (uu___1651_11709.smt_ok);
               umax_heuristic_ok = (uu___1651_11709.umax_heuristic_ok);
               tcenv = (uu___1651_11709.tcenv);
               wl_implicits = (uu___1651_11709.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11718 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11718
                 then
                   let uu____11721 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11721
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
                       (let uu____11728 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd1
                            probs1
                           in
                        solve env uu____11728)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1663_11734 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1663_11734.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1663_11734.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1663_11734.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1663_11734.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1663_11734.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1663_11734.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1663_11734.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1663_11734.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1663_11734.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11759 ->
                let uu____11769 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11834  ->
                          match uu____11834 with
                          | (c,uu____11844,uu____11845) -> c < probs.ctr))
                   in
                (match uu____11769 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11893 =
                            let uu____11898 =
                              FStar_List.map
                                (fun uu____11919  ->
                                   match uu____11919 with
                                   | (uu____11935,x,y) ->
                                       let uu____11946 = FStar_Thunk.force x
                                          in
                                       (uu____11946, y)) probs.wl_deferred
                               in
                            (uu____11898, (probs.wl_implicits))  in
                          Success uu____11893
                      | uu____11950 ->
                          let uu____11960 =
                            let uu___1681_11961 = probs  in
                            let uu____11962 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11983  ->
                                      match uu____11983 with
                                      | (uu____11991,uu____11992,y) -> y))
                               in
                            {
                              attempting = uu____11962;
                              wl_deferred = rest;
                              ctr = (uu___1681_11961.ctr);
                              defer_ok = (uu___1681_11961.defer_ok);
                              smt_ok = (uu___1681_11961.smt_ok);
                              umax_heuristic_ok =
                                (uu___1681_11961.umax_heuristic_ok);
                              tcenv = (uu___1681_11961.tcenv);
                              wl_implicits = (uu___1681_11961.wl_implicits)
                            }  in
                          solve env uu____11960))))

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
            let uu____12001 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12001 with
            | USolved wl1 ->
                let uu____12003 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12003
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12006 = defer_lit "" orig wl1  in
                solve env uu____12006

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
                  let uu____12057 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12057 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12060 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12073;
                  FStar_Syntax_Syntax.vars = uu____12074;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12077;
                  FStar_Syntax_Syntax.vars = uu____12078;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12091,uu____12092) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12100,FStar_Syntax_Syntax.Tm_uinst uu____12101) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12109 -> USolved wl

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
            ((let uu____12120 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12120
              then
                let uu____12125 = prob_to_string env orig  in
                let uu____12127 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12125 uu____12127
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
               let uu____12220 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12220 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12275 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12275
                then
                  let uu____12280 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12282 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12280 uu____12282
                else ());
               (let uu____12287 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12287 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12333 = eq_prob t1 t2 wl2  in
                         (match uu____12333 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12354 ->
                         let uu____12363 = eq_prob t1 t2 wl2  in
                         (match uu____12363 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12413 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12428 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12429 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12428, uu____12429)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12434 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12435 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12434, uu____12435)
                            in
                         (match uu____12413 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12466 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12466 with
                                | (t1_hd,t1_args) ->
                                    let uu____12511 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12511 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12577 =
                                              let uu____12584 =
                                                let uu____12595 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12595 :: t1_args  in
                                              let uu____12612 =
                                                let uu____12621 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12621 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12670  ->
                                                   fun uu____12671  ->
                                                     fun uu____12672  ->
                                                       match (uu____12670,
                                                               uu____12671,
                                                               uu____12672)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12722),
                                                          (a2,uu____12724))
                                                           ->
                                                           let uu____12761 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12761
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12584
                                                uu____12612
                                               in
                                            match uu____12577 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1835_12787 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1835_12787.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1835_12787.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1835_12787.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12798 =
                                                  solve env1 wl'  in
                                                (match uu____12798 with
                                                 | Success (uu____12801,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1844_12805
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1844_12805.attempting);
                                                            wl_deferred =
                                                              (uu___1844_12805.wl_deferred);
                                                            ctr =
                                                              (uu___1844_12805.ctr);
                                                            defer_ok =
                                                              (uu___1844_12805.defer_ok);
                                                            smt_ok =
                                                              (uu___1844_12805.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1844_12805.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1844_12805.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12806 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12838 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12838 with
                                | (t1_base,p1_opt) ->
                                    let uu____12874 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12874 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____12973 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____12973
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
                                               let uu____13026 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13026
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
                                               let uu____13058 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13058
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
                                               let uu____13090 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13090
                                           | uu____13093 -> t_base  in
                                         let uu____13110 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13110 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13124 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13124, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13131 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13131 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13167 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13167 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13203 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13203
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
                              let uu____13227 = combine t11 t21 wl2  in
                              (match uu____13227 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13260 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13260
                                     then
                                       let uu____13265 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13265
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13307 ts1 =
               match uu____13307 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13370 = pairwise out t wl2  in
                        (match uu____13370 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13406 =
               let uu____13417 = FStar_List.hd ts  in (uu____13417, [], wl1)
                in
             let uu____13426 = FStar_List.tl ts  in
             aux uu____13406 uu____13426  in
           let uu____13433 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13433 with
           | (this_flex,this_rigid) ->
               let uu____13459 =
                 let uu____13460 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13460.FStar_Syntax_Syntax.n  in
               (match uu____13459 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13485 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13485
                    then
                      let uu____13488 = destruct_flex_t this_flex wl  in
                      (match uu____13488 with
                       | (flex,wl1) ->
                           let uu____13495 = quasi_pattern env flex  in
                           (match uu____13495 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13514 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13514
                                  then
                                    let uu____13519 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13519
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13526 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1946_13529 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1946_13529.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1946_13529.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1946_13529.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1946_13529.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1946_13529.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1946_13529.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1946_13529.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1946_13529.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1946_13529.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13526)
                | uu____13530 ->
                    ((let uu____13532 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13532
                      then
                        let uu____13537 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13537
                      else ());
                     (let uu____13542 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13542 with
                      | (u,_args) ->
                          let uu____13585 =
                            let uu____13586 = FStar_Syntax_Subst.compress u
                               in
                            uu____13586.FStar_Syntax_Syntax.n  in
                          (match uu____13585 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13614 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13614 with
                                 | (u',uu____13633) ->
                                     let uu____13658 =
                                       let uu____13659 = whnf env u'  in
                                       uu____13659.FStar_Syntax_Syntax.n  in
                                     (match uu____13658 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13681 -> false)
                                  in
                               let uu____13683 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13706  ->
                                         match uu___26_13706 with
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
                                              | uu____13720 -> false)
                                         | uu____13724 -> false))
                                  in
                               (match uu____13683 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13739 = whnf env this_rigid
                                         in
                                      let uu____13740 =
                                        FStar_List.collect
                                          (fun uu___27_13746  ->
                                             match uu___27_13746 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13752 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13752]
                                             | uu____13756 -> [])
                                          bounds_probs
                                         in
                                      uu____13739 :: uu____13740  in
                                    let uu____13757 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13757 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13790 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13805 =
                                               let uu____13806 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13806.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13805 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13818 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13818)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13829 -> bound  in
                                           let uu____13830 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13830)  in
                                         (match uu____13790 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13865 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13865
                                                then
                                                  let wl'1 =
                                                    let uu___2006_13871 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2006_13871.wl_deferred);
                                                      ctr =
                                                        (uu___2006_13871.ctr);
                                                      defer_ok =
                                                        (uu___2006_13871.defer_ok);
                                                      smt_ok =
                                                        (uu___2006_13871.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2006_13871.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2006_13871.tcenv);
                                                      wl_implicits =
                                                        (uu___2006_13871.wl_implicits)
                                                    }  in
                                                  let uu____13872 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13872
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13878 =
                                                  solve_t env eq_prob
                                                    (let uu___2011_13880 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2011_13880.wl_deferred);
                                                       ctr =
                                                         (uu___2011_13880.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2011_13880.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2011_13880.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2011_13880.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13878 with
                                                | Success (uu____13882,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2017_13885 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2017_13885.wl_deferred);
                                                        ctr =
                                                          (uu___2017_13885.ctr);
                                                        defer_ok =
                                                          (uu___2017_13885.defer_ok);
                                                        smt_ok =
                                                          (uu___2017_13885.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2017_13885.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2017_13885.tcenv);
                                                        wl_implicits =
                                                          (uu___2017_13885.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2020_13887 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2020_13887.attempting);
                                                        wl_deferred =
                                                          (uu___2020_13887.wl_deferred);
                                                        ctr =
                                                          (uu___2020_13887.ctr);
                                                        defer_ok =
                                                          (uu___2020_13887.defer_ok);
                                                        smt_ok =
                                                          (uu___2020_13887.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2020_13887.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2020_13887.tcenv);
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
                                                    let uu____13903 =
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
                                                    ((let uu____13915 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13915
                                                      then
                                                        let uu____13920 =
                                                          let uu____13922 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13922
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13920
                                                      else ());
                                                     (let uu____13935 =
                                                        let uu____13950 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13950)
                                                         in
                                                      match uu____13935 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____13972))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13998 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13998
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
                                                                  let uu____14018
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14018))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14043 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14043
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
                                                                    let uu____14063
                                                                    =
                                                                    let uu____14068
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14068
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14063
                                                                    [] wl2
                                                                     in
                                                                  let uu____14074
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14074))))
                                                      | uu____14075 ->
                                                          let uu____14090 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14090 p)))))))
                           | uu____14097 when flip ->
                               let uu____14098 =
                                 let uu____14100 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14102 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14100 uu____14102
                                  in
                               failwith uu____14098
                           | uu____14105 ->
                               let uu____14106 =
                                 let uu____14108 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14110 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14108 uu____14110
                                  in
                               failwith uu____14106)))))

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
                      (fun uu____14146  ->
                         match uu____14146 with
                         | (x,i) ->
                             let uu____14165 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14165, i)) bs_lhs
                     in
                  let uu____14168 = lhs  in
                  match uu____14168 with
                  | (uu____14169,u_lhs,uu____14171) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14268 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14278 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14278, univ)
                             in
                          match uu____14268 with
                          | (k,univ) ->
                              let uu____14285 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14285 with
                               | (uu____14302,u,wl3) ->
                                   let uu____14305 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14305, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14331 =
                              let uu____14344 =
                                let uu____14355 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14355 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14406  ->
                                   fun uu____14407  ->
                                     match (uu____14406, uu____14407) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14508 =
                                           let uu____14515 =
                                             let uu____14518 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14518
                                              in
                                           copy_uvar u_lhs [] uu____14515 wl2
                                            in
                                         (match uu____14508 with
                                          | (uu____14547,t_a,wl3) ->
                                              let uu____14550 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14550 with
                                               | (uu____14569,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14344
                                ([], wl1)
                               in
                            (match uu____14331 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2131_14625 = ct  in
                                   let uu____14626 =
                                     let uu____14629 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14629
                                      in
                                   let uu____14644 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2131_14625.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2131_14625.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14626;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14644;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2131_14625.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2134_14662 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2134_14662.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2134_14662.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14665 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14665 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14703 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14703 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14714 =
                                          let uu____14719 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14719)  in
                                        TERM uu____14714  in
                                      let uu____14720 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14720 with
                                       | (sub_prob,wl3) ->
                                           let uu____14734 =
                                             let uu____14735 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14735
                                              in
                                           solve env uu____14734))
                             | (x,imp)::formals2 ->
                                 let uu____14757 =
                                   let uu____14764 =
                                     let uu____14767 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14767
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14764 wl1
                                    in
                                 (match uu____14757 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14788 =
                                          let uu____14791 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14791
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14788 u_x
                                         in
                                      let uu____14792 =
                                        let uu____14795 =
                                          let uu____14798 =
                                            let uu____14799 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14799, imp)  in
                                          [uu____14798]  in
                                        FStar_List.append bs_terms
                                          uu____14795
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14792 formals2 wl2)
                              in
                           let uu____14826 = occurs_check u_lhs arrow1  in
                           (match uu____14826 with
                            | (uu____14839,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14855 =
                                    mklstr
                                      (fun uu____14860  ->
                                         let uu____14861 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14861)
                                     in
                                  giveup_or_defer env orig wl uu____14855
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
              (let uu____14894 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14894
               then
                 let uu____14899 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14902 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14899 (rel_to_string (p_rel orig)) uu____14902
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15033 = rhs wl1 scope env1 subst1  in
                     (match uu____15033 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15056 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15056
                            then
                              let uu____15061 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15061
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15139 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15139 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2204_15141 = hd1  in
                       let uu____15142 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2204_15141.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2204_15141.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15142
                       }  in
                     let hd21 =
                       let uu___2207_15146 = hd2  in
                       let uu____15147 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2207_15146.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2207_15146.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15147
                       }  in
                     let uu____15150 =
                       let uu____15155 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15155
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15150 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15178 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15178
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15185 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15185 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15257 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15257
                                  in
                               ((let uu____15275 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15275
                                 then
                                   let uu____15280 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15282 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15280
                                     uu____15282
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15317 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15353 = aux wl [] env [] bs1 bs2  in
               match uu____15353 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15412 = attempt sub_probs wl2  in
                   solve env1 uu____15412)

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
            let uu___2245_15432 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2245_15432.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2245_15432.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15444 = try_solve env wl'  in
          match uu____15444 with
          | Success (uu____15445,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2254_15449 = wl  in
                  {
                    attempting = (uu___2254_15449.attempting);
                    wl_deferred = (uu___2254_15449.wl_deferred);
                    ctr = (uu___2254_15449.ctr);
                    defer_ok = (uu___2254_15449.defer_ok);
                    smt_ok = (uu___2254_15449.smt_ok);
                    umax_heuristic_ok = (uu___2254_15449.umax_heuristic_ok);
                    tcenv = (uu___2254_15449.tcenv);
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
        (let uu____15458 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15458 wl)

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
              let uu____15472 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15472 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15506 = lhs1  in
              match uu____15506 with
              | (uu____15509,ctx_u,uu____15511) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15519 ->
                        let uu____15520 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15520 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15569 = quasi_pattern env1 lhs1  in
              match uu____15569 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15603) ->
                  let uu____15608 = lhs1  in
                  (match uu____15608 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15623 = occurs_check ctx_u rhs1  in
                       (match uu____15623 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15674 =
                                let uu____15682 =
                                  let uu____15684 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15684
                                   in
                                FStar_Util.Inl uu____15682  in
                              (uu____15674, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15712 =
                                 let uu____15714 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15714  in
                               if uu____15712
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15741 =
                                    let uu____15749 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15749  in
                                  let uu____15755 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15741, uu____15755)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15799 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15799 with
              | (rhs_hd,args) ->
                  let uu____15842 = FStar_Util.prefix args  in
                  (match uu____15842 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15914 = lhs1  in
                       (match uu____15914 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15918 =
                              let uu____15929 =
                                let uu____15936 =
                                  let uu____15939 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15939
                                   in
                                copy_uvar u_lhs [] uu____15936 wl1  in
                              match uu____15929 with
                              | (uu____15966,t_last_arg,wl2) ->
                                  let uu____15969 =
                                    let uu____15976 =
                                      let uu____15977 =
                                        let uu____15986 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____15986]  in
                                      FStar_List.append bs_lhs uu____15977
                                       in
                                    copy_uvar u_lhs uu____15976 t_res_lhs wl2
                                     in
                                  (match uu____15969 with
                                   | (uu____16021,lhs',wl3) ->
                                       let uu____16024 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16024 with
                                        | (uu____16041,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15918 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16062 =
                                     let uu____16063 =
                                       let uu____16068 =
                                         let uu____16069 =
                                           let uu____16072 =
                                             let uu____16077 =
                                               let uu____16078 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16078]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16077
                                              in
                                           uu____16072
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16069
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16068)  in
                                     TERM uu____16063  in
                                   [uu____16062]  in
                                 let uu____16103 =
                                   let uu____16110 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16110 with
                                   | (p1,wl3) ->
                                       let uu____16130 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16130 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16103 with
                                  | (sub_probs,wl3) ->
                                      let uu____16162 =
                                        let uu____16163 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16163  in
                                      solve env1 uu____16162))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16197 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16197 with
                | (uu____16215,args) ->
                    (match args with | [] -> false | uu____16251 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16270 =
                  let uu____16271 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16271.FStar_Syntax_Syntax.n  in
                match uu____16270 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16275 -> true
                | uu____16291 -> false  in
              let uu____16293 = quasi_pattern env1 lhs1  in
              match uu____16293 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    mklstr
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
                          mklstr
                            (fun uu____16340  ->
                               let uu____16341 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16341)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16345 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16345
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16351 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16351
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16356 = lhs  in
                (match uu____16356 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16360 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16360 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16378 =
                              let uu____16382 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16382
                               in
                            FStar_All.pipe_right uu____16378
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16403 = occurs_check ctx_uv rhs1  in
                          (match uu____16403 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16432 =
                                   let uu____16433 =
                                     let uu____16435 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16435
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16433
                                    in
                                 giveup_or_defer env orig wl uu____16432
                               else
                                 (let uu____16443 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16443
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16450 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16450
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         mklstr
                                           (fun uu____16466  ->
                                              let uu____16467 =
                                                names_to_string1 fvs2  in
                                              let uu____16469 =
                                                names_to_string1 fvs1  in
                                              let uu____16471 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16467 uu____16469
                                                uu____16471)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16483 ->
                          if wl.defer_ok
                          then
                            let uu____16487 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16487
                          else
                            (let uu____16492 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16492 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16518 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16518
                             | (FStar_Util.Inl msg,uu____16520) ->
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
                  let uu____16538 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16538
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16544 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16544
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16566 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16566
                else
                  (let uu____16571 =
                     let uu____16588 = quasi_pattern env lhs  in
                     let uu____16595 = quasi_pattern env rhs  in
                     (uu____16588, uu____16595)  in
                   match uu____16571 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16638 = lhs  in
                       (match uu____16638 with
                        | ({ FStar_Syntax_Syntax.n = uu____16639;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16641;_},u_lhs,uu____16643)
                            ->
                            let uu____16646 = rhs  in
                            (match uu____16646 with
                             | (uu____16647,u_rhs,uu____16649) ->
                                 let uu____16650 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16650
                                 then
                                   let uu____16657 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16657
                                 else
                                   (let uu____16660 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16660 with
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
                                        let uu____16692 =
                                          let uu____16699 =
                                            let uu____16702 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16702
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16699
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16692 with
                                         | (uu____16714,w,wl1) ->
                                             let w_app =
                                               let uu____16720 =
                                                 let uu____16725 =
                                                   FStar_List.map
                                                     (fun uu____16736  ->
                                                        match uu____16736
                                                        with
                                                        | (z,uu____16744) ->
                                                            let uu____16749 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16749) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16725
                                                  in
                                               uu____16720
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16751 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16751
                                               then
                                                 let uu____16756 =
                                                   let uu____16760 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16762 =
                                                     let uu____16766 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16768 =
                                                       let uu____16772 =
                                                         term_to_string w  in
                                                       let uu____16774 =
                                                         let uu____16778 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16787 =
                                                           let uu____16791 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16800 =
                                                             let uu____16804
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16804]
                                                              in
                                                           uu____16791 ::
                                                             uu____16800
                                                            in
                                                         uu____16778 ::
                                                           uu____16787
                                                          in
                                                       uu____16772 ::
                                                         uu____16774
                                                        in
                                                     uu____16766 ::
                                                       uu____16768
                                                      in
                                                   uu____16760 :: uu____16762
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16756
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16821 =
                                                     let uu____16826 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16826)  in
                                                   TERM uu____16821  in
                                                 let uu____16827 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16827
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16835 =
                                                        let uu____16840 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16840)
                                                         in
                                                      TERM uu____16835  in
                                                    [s1; s2])
                                                  in
                                               let uu____16841 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16841))))))
                   | uu____16842 ->
                       let uu____16859 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16859)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16913 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16913
            then
              let uu____16918 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16920 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16922 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16924 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16918 uu____16920 uu____16922 uu____16924
            else ());
           (let uu____16935 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16935 with
            | (head1,args1) ->
                let uu____16978 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____16978 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17048 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17048 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17053 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17053)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17074 =
                         mklstr
                           (fun uu____17085  ->
                              let uu____17086 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17088 = args_to_string args1  in
                              let uu____17092 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17094 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17086 uu____17088 uu____17092
                                uu____17094)
                          in
                       giveup env1 uu____17074 orig
                     else
                       (let uu____17101 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17106 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17106 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17101
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2510_17110 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2510_17110.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2510_17110.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2510_17110.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2510_17110.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2510_17110.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2510_17110.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2510_17110.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2510_17110.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17120 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17120
                                    else solve env1 wl2))
                        else
                          (let uu____17125 = base_and_refinement env1 t1  in
                           match uu____17125 with
                           | (base1,refinement1) ->
                               let uu____17150 = base_and_refinement env1 t2
                                  in
                               (match uu____17150 with
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
                                           let uu____17315 =
                                             FStar_List.fold_right
                                               (fun uu____17355  ->
                                                  fun uu____17356  ->
                                                    match (uu____17355,
                                                            uu____17356)
                                                    with
                                                    | (((a1,uu____17408),
                                                        (a2,uu____17410)),
                                                       (probs,wl3)) ->
                                                        let uu____17459 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17459
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17315 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17502 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17502
                                                 then
                                                   let uu____17507 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17507
                                                 else ());
                                                (let uu____17513 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17513
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
                                                    (let uu____17540 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17540 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17556 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17556
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17564 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17564))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17589 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17589 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17605 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17605
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17613 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17613)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17641 =
                                           match uu____17641 with
                                           | (prob,reason) ->
                                               ((let uu____17658 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17658
                                                 then
                                                   let uu____17663 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17665 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____17663 uu____17665
                                                 else ());
                                                (let uu____17671 =
                                                   let uu____17680 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17683 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17680, uu____17683)
                                                    in
                                                 match uu____17671 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17696 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17696 with
                                                      | (head1',uu____17714)
                                                          ->
                                                          let uu____17739 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17739
                                                           with
                                                           | (head2',uu____17757)
                                                               ->
                                                               let uu____17782
                                                                 =
                                                                 let uu____17787
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17788
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17787,
                                                                   uu____17788)
                                                                  in
                                                               (match uu____17782
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17790
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17790
                                                                    then
                                                                    let uu____17795
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17797
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17799
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17801
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17795
                                                                    uu____17797
                                                                    uu____17799
                                                                    uu____17801
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17806
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2598_17814
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2598_17814.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2598_17814.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2598_17814.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2598_17814.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2598_17814.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2598_17814.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2598_17814.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2598_17814.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17816
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17816
                                                                    then
                                                                    let uu____17821
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17821
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17826 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17838 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17838 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17846 =
                                             let uu____17847 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17847.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17846 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17852 -> false  in
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
                                          | uu____17855 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17858 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2618_17894 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2618_17894.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2618_17894.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2618_17894.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2618_17894.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2618_17894.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2618_17894.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2618_17894.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2618_17894.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17970 = destruct_flex_t scrutinee wl1  in
             match uu____17970 with
             | ((_t,uv,_args),wl2) ->
                 let uu____17981 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____17981 with
                  | (xs,pat_term,uu____17997,uu____17998) ->
                      let uu____18003 =
                        FStar_List.fold_left
                          (fun uu____18026  ->
                             fun x  ->
                               match uu____18026 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18047 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18047 with
                                    | (uu____18066,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____18003 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18087 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18087 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2658_18104 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2658_18104.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2658_18104.umax_heuristic_ok);
                                    tcenv = (uu___2658_18104.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18115 = solve env1 wl'  in
                                (match uu____18115 with
                                 | Success (uu____18118,imps) ->
                                     let wl'1 =
                                       let uu___2666_18121 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2666_18121.wl_deferred);
                                         ctr = (uu___2666_18121.ctr);
                                         defer_ok =
                                           (uu___2666_18121.defer_ok);
                                         smt_ok = (uu___2666_18121.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2666_18121.umax_heuristic_ok);
                                         tcenv = (uu___2666_18121.tcenv);
                                         wl_implicits =
                                           (uu___2666_18121.wl_implicits)
                                       }  in
                                     let uu____18122 = solve env1 wl'1  in
                                     (match uu____18122 with
                                      | Success (uu____18125,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2674_18129 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2674_18129.attempting);
                                                 wl_deferred =
                                                   (uu___2674_18129.wl_deferred);
                                                 ctr = (uu___2674_18129.ctr);
                                                 defer_ok =
                                                   (uu___2674_18129.defer_ok);
                                                 smt_ok =
                                                   (uu___2674_18129.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2674_18129.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2674_18129.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18130 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18136 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18159 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18159
                 then
                   let uu____18164 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18166 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18164 uu____18166
                 else ());
                (let uu____18171 =
                   let uu____18192 =
                     let uu____18201 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18201)  in
                   let uu____18208 =
                     let uu____18217 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18217)  in
                   (uu____18192, uu____18208)  in
                 match uu____18171 with
                 | ((uu____18247,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18250;
                                   FStar_Syntax_Syntax.vars = uu____18251;_}),
                    (s,t)) ->
                     let uu____18322 =
                       let uu____18324 = is_flex scrutinee  in
                       Prims.op_Negation uu____18324  in
                     if uu____18322
                     then
                       ((let uu____18335 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18335
                         then
                           let uu____18340 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18340
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18359 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18359
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18374 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18374
                           then
                             let uu____18379 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18381 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18379 uu____18381
                           else ());
                          (let pat_discriminates uu___28_18406 =
                             match uu___28_18406 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18422;
                                  FStar_Syntax_Syntax.p = uu____18423;_},FStar_Pervasives_Native.None
                                ,uu____18424) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18438;
                                  FStar_Syntax_Syntax.p = uu____18439;_},FStar_Pervasives_Native.None
                                ,uu____18440) -> true
                             | uu____18467 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18570 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18570 with
                                       | (uu____18572,uu____18573,t') ->
                                           let uu____18591 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18591 with
                                            | (FullMatch ,uu____18603) ->
                                                true
                                            | (HeadMatch
                                               uu____18617,uu____18618) ->
                                                true
                                            | uu____18633 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18670 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18670
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18681 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18681 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18769,uu____18770) ->
                                       branches1
                                   | uu____18915 -> branches  in
                                 let uu____18970 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____18979 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____18979 with
                                        | (p,uu____18983,uu____18984) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19013  -> FStar_Util.Inr _19013)
                                   uu____18970))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19043 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19043 with
                                | (p,uu____19052,e) ->
                                    ((let uu____19071 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19071
                                      then
                                        let uu____19076 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19078 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19076 uu____19078
                                      else ());
                                     (let uu____19083 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19098  -> FStar_Util.Inr _19098)
                                        uu____19083)))))
                 | ((s,t),(uu____19101,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19104;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19105;_}))
                     ->
                     let uu____19174 =
                       let uu____19176 = is_flex scrutinee  in
                       Prims.op_Negation uu____19176  in
                     if uu____19174
                     then
                       ((let uu____19187 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19187
                         then
                           let uu____19192 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19192
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19211 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19211
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19226 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19226
                           then
                             let uu____19231 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19233 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19231 uu____19233
                           else ());
                          (let pat_discriminates uu___28_19258 =
                             match uu___28_19258 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19274;
                                  FStar_Syntax_Syntax.p = uu____19275;_},FStar_Pervasives_Native.None
                                ,uu____19276) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19290;
                                  FStar_Syntax_Syntax.p = uu____19291;_},FStar_Pervasives_Native.None
                                ,uu____19292) -> true
                             | uu____19319 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19422 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19422 with
                                       | (uu____19424,uu____19425,t') ->
                                           let uu____19443 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19443 with
                                            | (FullMatch ,uu____19455) ->
                                                true
                                            | (HeadMatch
                                               uu____19469,uu____19470) ->
                                                true
                                            | uu____19485 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19522 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19522
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19533 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19533 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19621,uu____19622) ->
                                       branches1
                                   | uu____19767 -> branches  in
                                 let uu____19822 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19831 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19831 with
                                        | (p,uu____19835,uu____19836) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19865  -> FStar_Util.Inr _19865)
                                   uu____19822))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19895 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19895 with
                                | (p,uu____19904,e) ->
                                    ((let uu____19923 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19923
                                      then
                                        let uu____19928 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19930 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19928 uu____19930
                                      else ());
                                     (let uu____19935 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19950  -> FStar_Util.Inr _19950)
                                        uu____19935)))))
                 | uu____19951 ->
                     ((let uu____19973 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19973
                       then
                         let uu____19978 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____19980 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____19978 uu____19980
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20026 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20026
            then
              let uu____20031 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20033 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20035 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20037 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20031 uu____20033 uu____20035 uu____20037
            else ());
           (let uu____20042 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20042 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20073,uu____20074) ->
                     let rec may_relate head3 =
                       let uu____20102 =
                         let uu____20103 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20103.FStar_Syntax_Syntax.n  in
                       match uu____20102 with
                       | FStar_Syntax_Syntax.Tm_name uu____20107 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20109 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20134 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20134 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20136 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20139
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20140 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20143,uu____20144) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20186) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20192) ->
                           may_relate t
                       | uu____20197 -> false  in
                     let uu____20199 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20199 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20212 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20212
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20222 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20222
                          then
                            let uu____20225 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20225 with
                             | (guard,wl2) ->
                                 let uu____20232 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20232)
                          else
                            (let uu____20235 =
                               mklstr
                                 (fun uu____20246  ->
                                    let uu____20247 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20249 =
                                      let uu____20251 =
                                        let uu____20255 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20255
                                          (fun x  ->
                                             let uu____20262 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20262)
                                         in
                                      FStar_Util.dflt "" uu____20251  in
                                    let uu____20267 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20269 =
                                      let uu____20271 =
                                        let uu____20275 =
                                          delta_depth_of_term env1 head2  in
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
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20247 uu____20249 uu____20267
                                      uu____20269)
                                in
                             giveup env1 uu____20235 orig))
                 | (HeadMatch (true ),uu____20288) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20303 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20303 with
                        | (guard,wl2) ->
                            let uu____20310 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20310)
                     else
                       (let uu____20313 =
                          mklstr
                            (fun uu____20320  ->
                               let uu____20321 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20323 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20321 uu____20323)
                           in
                        giveup env1 uu____20313 orig)
                 | (uu____20326,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2849_20340 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2849_20340.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2849_20340.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2849_20340.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2849_20340.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2849_20340.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2849_20340.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2849_20340.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2849_20340.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20367 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20367
          then
            let uu____20370 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20370
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20376 =
                let uu____20379 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20379  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20376 t1);
             (let uu____20398 =
                let uu____20401 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20401  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20398 t2);
             (let uu____20420 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20420
              then
                let uu____20424 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20426 =
                  let uu____20428 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20430 =
                    let uu____20432 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20432  in
                  Prims.op_Hat uu____20428 uu____20430  in
                let uu____20435 =
                  let uu____20437 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20439 =
                    let uu____20441 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20441  in
                  Prims.op_Hat uu____20437 uu____20439  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20424 uu____20426 uu____20435
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20448,uu____20449) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20465,FStar_Syntax_Syntax.Tm_delayed uu____20466) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20482,uu____20483) ->
                  let uu____20510 =
                    let uu___2880_20511 = problem  in
                    let uu____20512 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2880_20511.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20512;
                      FStar_TypeChecker_Common.relation =
                        (uu___2880_20511.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2880_20511.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2880_20511.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2880_20511.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2880_20511.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2880_20511.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2880_20511.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2880_20511.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20510 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20513,uu____20514) ->
                  let uu____20521 =
                    let uu___2886_20522 = problem  in
                    let uu____20523 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2886_20522.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20523;
                      FStar_TypeChecker_Common.relation =
                        (uu___2886_20522.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2886_20522.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2886_20522.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2886_20522.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2886_20522.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2886_20522.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2886_20522.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2886_20522.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20521 wl
              | (uu____20524,FStar_Syntax_Syntax.Tm_ascribed uu____20525) ->
                  let uu____20552 =
                    let uu___2892_20553 = problem  in
                    let uu____20554 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2892_20553.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2892_20553.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2892_20553.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20554;
                      FStar_TypeChecker_Common.element =
                        (uu___2892_20553.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2892_20553.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2892_20553.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2892_20553.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2892_20553.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2892_20553.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20552 wl
              | (uu____20555,FStar_Syntax_Syntax.Tm_meta uu____20556) ->
                  let uu____20563 =
                    let uu___2898_20564 = problem  in
                    let uu____20565 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2898_20564.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2898_20564.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2898_20564.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20565;
                      FStar_TypeChecker_Common.element =
                        (uu___2898_20564.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2898_20564.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2898_20564.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2898_20564.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2898_20564.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2898_20564.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20563 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20567),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20569)) ->
                  let uu____20578 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20578
              | (FStar_Syntax_Syntax.Tm_bvar uu____20579,uu____20580) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20582,FStar_Syntax_Syntax.Tm_bvar uu____20583) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20653 =
                    match uu___29_20653 with
                    | [] -> c
                    | bs ->
                        let uu____20681 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20681
                     in
                  let uu____20692 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20692 with
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
                                    let uu____20841 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20841
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
                  let mk_t t l uu___30_20930 =
                    match uu___30_20930 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____20972 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____20972 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21117 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21118 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21117
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21118 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21120,uu____21121) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21152 -> true
                    | uu____21172 -> false  in
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
                      (let uu____21232 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3000_21240 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3000_21240.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3000_21240.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3000_21240.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3000_21240.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3000_21240.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3000_21240.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3000_21240.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3000_21240.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3000_21240.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3000_21240.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3000_21240.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3000_21240.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3000_21240.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3000_21240.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3000_21240.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3000_21240.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3000_21240.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3000_21240.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3000_21240.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3000_21240.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3000_21240.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3000_21240.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3000_21240.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3000_21240.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3000_21240.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3000_21240.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3000_21240.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3000_21240.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3000_21240.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3000_21240.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3000_21240.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3000_21240.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3000_21240.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3000_21240.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3000_21240.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3000_21240.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3000_21240.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3000_21240.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3000_21240.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3000_21240.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3000_21240.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3000_21240.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3000_21240.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3000_21240.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21232 with
                       | (uu____21245,ty,uu____21247) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21256 =
                                 let uu____21257 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21257.FStar_Syntax_Syntax.n  in
                               match uu____21256 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21260 ->
                                   let uu____21267 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21267
                               | uu____21268 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21271 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21271
                             then
                               let uu____21276 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21278 =
                                 let uu____21280 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21280
                                  in
                               let uu____21281 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21276 uu____21278 uu____21281
                             else ());
                            r1))
                     in
                  let uu____21286 =
                    let uu____21303 = maybe_eta t1  in
                    let uu____21310 = maybe_eta t2  in
                    (uu____21303, uu____21310)  in
                  (match uu____21286 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3021_21352 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3021_21352.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3021_21352.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3021_21352.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3021_21352.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3021_21352.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3021_21352.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3021_21352.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3021_21352.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21373 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21373
                       then
                         let uu____21376 = destruct_flex_t not_abs wl  in
                         (match uu____21376 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21393 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21393.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21393.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21393.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21393.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21393.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21393.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21393.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21393.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21396 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21396 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21419 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21419
                       then
                         let uu____21422 = destruct_flex_t not_abs wl  in
                         (match uu____21422 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21439 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21439.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21439.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21439.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21439.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21439.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21439.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21439.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21439.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21442 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21442 orig))
                   | uu____21445 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21463,FStar_Syntax_Syntax.Tm_abs uu____21464) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21495 -> true
                    | uu____21515 -> false  in
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
                      (let uu____21575 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3000_21583 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3000_21583.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3000_21583.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3000_21583.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3000_21583.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3000_21583.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3000_21583.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3000_21583.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3000_21583.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3000_21583.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3000_21583.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3000_21583.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3000_21583.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3000_21583.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3000_21583.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3000_21583.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3000_21583.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3000_21583.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3000_21583.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3000_21583.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3000_21583.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3000_21583.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3000_21583.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3000_21583.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3000_21583.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3000_21583.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3000_21583.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3000_21583.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3000_21583.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3000_21583.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3000_21583.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3000_21583.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3000_21583.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3000_21583.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3000_21583.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3000_21583.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3000_21583.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3000_21583.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3000_21583.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3000_21583.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3000_21583.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3000_21583.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3000_21583.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3000_21583.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3000_21583.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21575 with
                       | (uu____21588,ty,uu____21590) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21599 =
                                 let uu____21600 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21600.FStar_Syntax_Syntax.n  in
                               match uu____21599 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21603 ->
                                   let uu____21610 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21610
                               | uu____21611 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21614 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21614
                             then
                               let uu____21619 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21621 =
                                 let uu____21623 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21623
                                  in
                               let uu____21624 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21619 uu____21621 uu____21624
                             else ());
                            r1))
                     in
                  let uu____21629 =
                    let uu____21646 = maybe_eta t1  in
                    let uu____21653 = maybe_eta t2  in
                    (uu____21646, uu____21653)  in
                  (match uu____21629 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3021_21695 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3021_21695.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3021_21695.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3021_21695.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3021_21695.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3021_21695.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3021_21695.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3021_21695.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3021_21695.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21716 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21716
                       then
                         let uu____21719 = destruct_flex_t not_abs wl  in
                         (match uu____21719 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21736 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21736.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21736.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21736.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21736.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21736.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21736.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21736.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21736.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21739 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21739 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21762 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21762
                       then
                         let uu____21765 = destruct_flex_t not_abs wl  in
                         (match uu____21765 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21782 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21782.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21782.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21782.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21782.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21782.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21782.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21782.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21782.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21785 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21785 orig))
                   | uu____21788 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21818 =
                    let uu____21823 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21823 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3061_21851 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3061_21851.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3061_21851.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3063_21853 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3063_21853.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3063_21853.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21854,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3061_21869 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3061_21869.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3061_21869.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3063_21871 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3063_21871.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3063_21871.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21872 -> (x1, x2)  in
                  (match uu____21818 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21891 = as_refinement false env t11  in
                       (match uu____21891 with
                        | (x12,phi11) ->
                            let uu____21899 = as_refinement false env t21  in
                            (match uu____21899 with
                             | (x22,phi21) ->
                                 ((let uu____21908 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21908
                                   then
                                     ((let uu____21913 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21915 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21917 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21913
                                         uu____21915 uu____21917);
                                      (let uu____21920 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21922 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21924 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21920
                                         uu____21922 uu____21924))
                                   else ());
                                  (let uu____21929 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21929 with
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
                                         let uu____22000 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22000
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22012 =
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
                                         (let uu____22025 =
                                            let uu____22028 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22028
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22025
                                            (p_guard base_prob));
                                         (let uu____22047 =
                                            let uu____22050 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22050
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22047
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22069 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22069)
                                          in
                                       let has_uvars =
                                         (let uu____22074 =
                                            let uu____22076 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22076
                                             in
                                          Prims.op_Negation uu____22074) ||
                                           (let uu____22080 =
                                              let uu____22082 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22082
                                               in
                                            Prims.op_Negation uu____22080)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22086 =
                                           let uu____22091 =
                                             let uu____22100 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22100]  in
                                           mk_t_problem wl1 uu____22091 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22086 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22123 =
                                                solve env1
                                                  (let uu___3106_22125 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3106_22125.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3106_22125.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3106_22125.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3106_22125.tcenv);
                                                     wl_implicits =
                                                       (uu___3106_22125.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22123 with
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
                                               | Success uu____22140 ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22149 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22149
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3119_22158 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3119_22158.attempting);
                                                         wl_deferred =
                                                           (uu___3119_22158.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3119_22158.defer_ok);
                                                         smt_ok =
                                                           (uu___3119_22158.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3119_22158.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3119_22158.tcenv);
                                                         wl_implicits =
                                                           (uu___3119_22158.wl_implicits)
                                                       }  in
                                                     let uu____22160 =
                                                       attempt [base_prob]
                                                         wl4
                                                        in
                                                     solve env1 uu____22160))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22163,FStar_Syntax_Syntax.Tm_uvar uu____22164) ->
                  let uu____22189 = destruct_flex_t t1 wl  in
                  (match uu____22189 with
                   | (f1,wl1) ->
                       let uu____22196 = destruct_flex_t t2 wl1  in
                       (match uu____22196 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22203;
                    FStar_Syntax_Syntax.pos = uu____22204;
                    FStar_Syntax_Syntax.vars = uu____22205;_},uu____22206),FStar_Syntax_Syntax.Tm_uvar
                 uu____22207) ->
                  let uu____22256 = destruct_flex_t t1 wl  in
                  (match uu____22256 with
                   | (f1,wl1) ->
                       let uu____22263 = destruct_flex_t t2 wl1  in
                       (match uu____22263 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22270,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22271;
                    FStar_Syntax_Syntax.pos = uu____22272;
                    FStar_Syntax_Syntax.vars = uu____22273;_},uu____22274))
                  ->
                  let uu____22323 = destruct_flex_t t1 wl  in
                  (match uu____22323 with
                   | (f1,wl1) ->
                       let uu____22330 = destruct_flex_t t2 wl1  in
                       (match uu____22330 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22337;
                    FStar_Syntax_Syntax.pos = uu____22338;
                    FStar_Syntax_Syntax.vars = uu____22339;_},uu____22340),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22341;
                    FStar_Syntax_Syntax.pos = uu____22342;
                    FStar_Syntax_Syntax.vars = uu____22343;_},uu____22344))
                  ->
                  let uu____22417 = destruct_flex_t t1 wl  in
                  (match uu____22417 with
                   | (f1,wl1) ->
                       let uu____22424 = destruct_flex_t t2 wl1  in
                       (match uu____22424 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22431,uu____22432) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22445 = destruct_flex_t t1 wl  in
                  (match uu____22445 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22452;
                    FStar_Syntax_Syntax.pos = uu____22453;
                    FStar_Syntax_Syntax.vars = uu____22454;_},uu____22455),uu____22456)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22493 = destruct_flex_t t1 wl  in
                  (match uu____22493 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22500,FStar_Syntax_Syntax.Tm_uvar uu____22501) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22514,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22515;
                    FStar_Syntax_Syntax.pos = uu____22516;
                    FStar_Syntax_Syntax.vars = uu____22517;_},uu____22518))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22555,FStar_Syntax_Syntax.Tm_arrow uu____22556) ->
                  solve_t' env
                    (let uu___3219_22584 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3219_22584.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3219_22584.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3219_22584.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3219_22584.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3219_22584.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3219_22584.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3219_22584.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3219_22584.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3219_22584.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22585;
                    FStar_Syntax_Syntax.pos = uu____22586;
                    FStar_Syntax_Syntax.vars = uu____22587;_},uu____22588),FStar_Syntax_Syntax.Tm_arrow
                 uu____22589) ->
                  solve_t' env
                    (let uu___3219_22641 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3219_22641.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3219_22641.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3219_22641.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3219_22641.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3219_22641.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3219_22641.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3219_22641.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3219_22641.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3219_22641.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22642,FStar_Syntax_Syntax.Tm_uvar uu____22643) ->
                  let uu____22656 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22656
              | (uu____22657,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22658;
                    FStar_Syntax_Syntax.pos = uu____22659;
                    FStar_Syntax_Syntax.vars = uu____22660;_},uu____22661))
                  ->
                  let uu____22698 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22698
              | (FStar_Syntax_Syntax.Tm_uvar uu____22699,uu____22700) ->
                  let uu____22713 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22713
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22714;
                    FStar_Syntax_Syntax.pos = uu____22715;
                    FStar_Syntax_Syntax.vars = uu____22716;_},uu____22717),uu____22718)
                  ->
                  let uu____22755 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22755
              | (FStar_Syntax_Syntax.Tm_refine uu____22756,uu____22757) ->
                  let t21 =
                    let uu____22765 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22765  in
                  solve_t env
                    (let uu___3254_22791 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3254_22791.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3254_22791.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3254_22791.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3254_22791.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3254_22791.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3254_22791.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3254_22791.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3254_22791.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3254_22791.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22792,FStar_Syntax_Syntax.Tm_refine uu____22793) ->
                  let t11 =
                    let uu____22801 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22801  in
                  solve_t env
                    (let uu___3261_22827 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3261_22827.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3261_22827.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3261_22827.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3261_22827.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3261_22827.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3261_22827.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3261_22827.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3261_22827.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3261_22827.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22909 =
                    let uu____22910 = guard_of_prob env wl problem t1 t2  in
                    match uu____22910 with
                    | (guard,wl1) ->
                        let uu____22917 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22917
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23136 = br1  in
                        (match uu____23136 with
                         | (p1,w1,uu____23165) ->
                             let uu____23182 = br2  in
                             (match uu____23182 with
                              | (p2,w2,uu____23205) ->
                                  let uu____23210 =
                                    let uu____23212 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23212  in
                                  if uu____23210
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23239 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23239 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23276 = br2  in
                                         (match uu____23276 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23309 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23309
                                                 in
                                              let uu____23314 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23345,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23366) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23425 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23425 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23314
                                                (fun uu____23497  ->
                                                   match uu____23497 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23534 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23534
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23555
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23555
                                                              then
                                                                let uu____23560
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23562
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23560
                                                                  uu____23562
                                                              else ());
                                                             (let uu____23568
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23568
                                                                (fun
                                                                   uu____23604
                                                                    ->
                                                                   match uu____23604
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
                    | uu____23733 -> FStar_Pervasives_Native.None  in
                  let uu____23774 = solve_branches wl brs1 brs2  in
                  (match uu____23774 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23800 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23800 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23827 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23827 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23861 =
                                FStar_List.map
                                  (fun uu____23873  ->
                                     match uu____23873 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23861  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23882 =
                              let uu____23883 =
                                let uu____23884 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23884
                                  (let uu___3360_23892 = wl3  in
                                   {
                                     attempting =
                                       (uu___3360_23892.attempting);
                                     wl_deferred =
                                       (uu___3360_23892.wl_deferred);
                                     ctr = (uu___3360_23892.ctr);
                                     defer_ok = (uu___3360_23892.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3360_23892.umax_heuristic_ok);
                                     tcenv = (uu___3360_23892.tcenv);
                                     wl_implicits =
                                       (uu___3360_23892.wl_implicits)
                                   })
                                 in
                              solve env uu____23883  in
                            (match uu____23882 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23897 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____23906 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____23906 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____23909,uu____23910) ->
                  let head1 =
                    let uu____23934 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23934
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23980 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23980
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24026 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24026
                    then
                      let uu____24030 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24032 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24034 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24030 uu____24032 uu____24034
                    else ());
                   (let no_free_uvars t =
                      (let uu____24048 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24048) &&
                        (let uu____24052 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24052)
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
                      let uu____24071 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24071 = FStar_Syntax_Util.Equal  in
                    let uu____24072 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24072
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24076 = equal t1 t2  in
                         (if uu____24076
                          then
                            let uu____24079 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24079
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24084 =
                            let uu____24091 = equal t1 t2  in
                            if uu____24091
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24104 = mk_eq2 wl env orig t1 t2  in
                               match uu____24104 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24084 with
                          | (guard,wl1) ->
                              let uu____24125 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24125))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24128,uu____24129) ->
                  let head1 =
                    let uu____24137 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24137
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24183 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24183
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24229 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24229
                    then
                      let uu____24233 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24235 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24237 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24233 uu____24235 uu____24237
                    else ());
                   (let no_free_uvars t =
                      (let uu____24251 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24251) &&
                        (let uu____24255 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24255)
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
                      let uu____24274 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24274 = FStar_Syntax_Util.Equal  in
                    let uu____24275 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24275
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24279 = equal t1 t2  in
                         (if uu____24279
                          then
                            let uu____24282 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24282
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24287 =
                            let uu____24294 = equal t1 t2  in
                            if uu____24294
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24307 = mk_eq2 wl env orig t1 t2  in
                               match uu____24307 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24287 with
                          | (guard,wl1) ->
                              let uu____24328 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24328))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24331,uu____24332) ->
                  let head1 =
                    let uu____24334 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24334
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24380 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24380
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24426 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24426
                    then
                      let uu____24430 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24432 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24434 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24430 uu____24432 uu____24434
                    else ());
                   (let no_free_uvars t =
                      (let uu____24448 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24448) &&
                        (let uu____24452 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24452)
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
                      let uu____24471 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24471 = FStar_Syntax_Util.Equal  in
                    let uu____24472 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24472
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24476 = equal t1 t2  in
                         (if uu____24476
                          then
                            let uu____24479 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24479
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24484 =
                            let uu____24491 = equal t1 t2  in
                            if uu____24491
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24504 = mk_eq2 wl env orig t1 t2  in
                               match uu____24504 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24484 with
                          | (guard,wl1) ->
                              let uu____24525 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24525))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24528,uu____24529) ->
                  let head1 =
                    let uu____24531 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24531
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24577 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24577
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24623 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24623
                    then
                      let uu____24627 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24629 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24631 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24627 uu____24629 uu____24631
                    else ());
                   (let no_free_uvars t =
                      (let uu____24645 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24645) &&
                        (let uu____24649 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24649)
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
                      let uu____24668 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24668 = FStar_Syntax_Util.Equal  in
                    let uu____24669 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24669
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24673 = equal t1 t2  in
                         (if uu____24673
                          then
                            let uu____24676 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24676
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24681 =
                            let uu____24688 = equal t1 t2  in
                            if uu____24688
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24701 = mk_eq2 wl env orig t1 t2  in
                               match uu____24701 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24681 with
                          | (guard,wl1) ->
                              let uu____24722 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24722))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24725,uu____24726) ->
                  let head1 =
                    let uu____24728 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24728
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24774 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24774
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24820 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24820
                    then
                      let uu____24824 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24826 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24828 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24824 uu____24826 uu____24828
                    else ());
                   (let no_free_uvars t =
                      (let uu____24842 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24842) &&
                        (let uu____24846 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24846)
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
                      let uu____24865 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24865 = FStar_Syntax_Util.Equal  in
                    let uu____24866 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24866
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24870 = equal t1 t2  in
                         (if uu____24870
                          then
                            let uu____24873 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24873
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24878 =
                            let uu____24885 = equal t1 t2  in
                            if uu____24885
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24898 = mk_eq2 wl env orig t1 t2  in
                               match uu____24898 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24878 with
                          | (guard,wl1) ->
                              let uu____24919 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24919))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24922,uu____24923) ->
                  let head1 =
                    let uu____24941 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24941
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24987 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24987
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25033 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25033
                    then
                      let uu____25037 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25039 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25041 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25037 uu____25039 uu____25041
                    else ());
                   (let no_free_uvars t =
                      (let uu____25055 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25055) &&
                        (let uu____25059 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25059)
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
                      let uu____25078 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25078 = FStar_Syntax_Util.Equal  in
                    let uu____25079 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25079
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25083 = equal t1 t2  in
                         (if uu____25083
                          then
                            let uu____25086 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25086
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25091 =
                            let uu____25098 = equal t1 t2  in
                            if uu____25098
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25111 = mk_eq2 wl env orig t1 t2  in
                               match uu____25111 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25091 with
                          | (guard,wl1) ->
                              let uu____25132 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25132))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25135,FStar_Syntax_Syntax.Tm_match uu____25136) ->
                  let head1 =
                    let uu____25160 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25160
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25206 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25206
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25252 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25252
                    then
                      let uu____25256 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25258 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25260 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25256 uu____25258 uu____25260
                    else ());
                   (let no_free_uvars t =
                      (let uu____25274 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25274) &&
                        (let uu____25278 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25278)
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
                      let uu____25297 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25297 = FStar_Syntax_Util.Equal  in
                    let uu____25298 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25298
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25302 = equal t1 t2  in
                         (if uu____25302
                          then
                            let uu____25305 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25305
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25310 =
                            let uu____25317 = equal t1 t2  in
                            if uu____25317
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25330 = mk_eq2 wl env orig t1 t2  in
                               match uu____25330 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25310 with
                          | (guard,wl1) ->
                              let uu____25351 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25351))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25354,FStar_Syntax_Syntax.Tm_uinst uu____25355) ->
                  let head1 =
                    let uu____25363 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25363
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25409 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25409
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25455 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25455
                    then
                      let uu____25459 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25461 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25463 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25459 uu____25461 uu____25463
                    else ());
                   (let no_free_uvars t =
                      (let uu____25477 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25477) &&
                        (let uu____25481 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25481)
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
                      let uu____25500 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25500 = FStar_Syntax_Util.Equal  in
                    let uu____25501 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25501
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25505 = equal t1 t2  in
                         (if uu____25505
                          then
                            let uu____25508 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25508
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25513 =
                            let uu____25520 = equal t1 t2  in
                            if uu____25520
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25533 = mk_eq2 wl env orig t1 t2  in
                               match uu____25533 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25513 with
                          | (guard,wl1) ->
                              let uu____25554 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25554))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25557,FStar_Syntax_Syntax.Tm_name uu____25558) ->
                  let head1 =
                    let uu____25560 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25560
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25606 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25606
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25646 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25646
                    then
                      let uu____25650 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25652 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25654 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25650 uu____25652 uu____25654
                    else ());
                   (let no_free_uvars t =
                      (let uu____25668 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25668) &&
                        (let uu____25672 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25672)
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
                      let uu____25691 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25691 = FStar_Syntax_Util.Equal  in
                    let uu____25692 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25692
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25696 = equal t1 t2  in
                         (if uu____25696
                          then
                            let uu____25699 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25699
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25704 =
                            let uu____25711 = equal t1 t2  in
                            if uu____25711
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25724 = mk_eq2 wl env orig t1 t2  in
                               match uu____25724 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25704 with
                          | (guard,wl1) ->
                              let uu____25745 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25745))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25748,FStar_Syntax_Syntax.Tm_constant uu____25749) ->
                  let head1 =
                    let uu____25751 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25751
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25791 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25791
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25831 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25831
                    then
                      let uu____25835 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25837 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25839 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25835 uu____25837 uu____25839
                    else ());
                   (let no_free_uvars t =
                      (let uu____25853 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25853) &&
                        (let uu____25857 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25857)
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
                      let uu____25876 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25876 = FStar_Syntax_Util.Equal  in
                    let uu____25877 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25877
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25881 = equal t1 t2  in
                         (if uu____25881
                          then
                            let uu____25884 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25884
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25889 =
                            let uu____25896 = equal t1 t2  in
                            if uu____25896
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25909 = mk_eq2 wl env orig t1 t2  in
                               match uu____25909 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25889 with
                          | (guard,wl1) ->
                              let uu____25930 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25930))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25933,FStar_Syntax_Syntax.Tm_fvar uu____25934) ->
                  let head1 =
                    let uu____25936 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25936
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25982 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25982
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26028 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26028
                    then
                      let uu____26032 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26034 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26036 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26032 uu____26034 uu____26036
                    else ());
                   (let no_free_uvars t =
                      (let uu____26050 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26050) &&
                        (let uu____26054 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26054)
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
                      let uu____26073 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26073 = FStar_Syntax_Util.Equal  in
                    let uu____26074 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26074
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26078 = equal t1 t2  in
                         (if uu____26078
                          then
                            let uu____26081 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26081
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26086 =
                            let uu____26093 = equal t1 t2  in
                            if uu____26093
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26106 = mk_eq2 wl env orig t1 t2  in
                               match uu____26106 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26086 with
                          | (guard,wl1) ->
                              let uu____26127 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26127))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26130,FStar_Syntax_Syntax.Tm_app uu____26131) ->
                  let head1 =
                    let uu____26149 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26149
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26189 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26189
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26229 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26229
                    then
                      let uu____26233 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26235 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26237 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26233 uu____26235 uu____26237
                    else ());
                   (let no_free_uvars t =
                      (let uu____26251 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26251) &&
                        (let uu____26255 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26255)
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
                      let uu____26274 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26274 = FStar_Syntax_Util.Equal  in
                    let uu____26275 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26275
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26279 = equal t1 t2  in
                         (if uu____26279
                          then
                            let uu____26282 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26282
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26287 =
                            let uu____26294 = equal t1 t2  in
                            if uu____26294
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26307 = mk_eq2 wl env orig t1 t2  in
                               match uu____26307 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26287 with
                          | (guard,wl1) ->
                              let uu____26328 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26328))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26331,FStar_Syntax_Syntax.Tm_let uu____26332) ->
                  let uu____26359 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26359
                  then
                    let uu____26362 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26362
                  else
                    (let uu____26365 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26365 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26368,uu____26369) ->
                  let uu____26383 =
                    let uu____26389 =
                      let uu____26391 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26393 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26395 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26397 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26391 uu____26393 uu____26395 uu____26397
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26389)
                     in
                  FStar_Errors.raise_error uu____26383
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26401,FStar_Syntax_Syntax.Tm_let uu____26402) ->
                  let uu____26416 =
                    let uu____26422 =
                      let uu____26424 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26426 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26428 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26430 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26424 uu____26426 uu____26428 uu____26430
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26422)
                     in
                  FStar_Errors.raise_error uu____26416
                    t1.FStar_Syntax_Syntax.pos
              | uu____26434 ->
                  let uu____26439 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26439 orig))))

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
          (let uu____26505 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26505
           then
             let uu____26510 =
               let uu____26512 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26512  in
             let uu____26513 =
               let uu____26515 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26515  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26510 uu____26513
           else ());
          (let uu____26519 =
             let uu____26521 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26521  in
           if uu____26519
           then
             let uu____26524 =
               mklstr
                 (fun uu____26531  ->
                    let uu____26532 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26534 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26532 uu____26534)
                in
             giveup env uu____26524 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26556 =
                  mklstr
                    (fun uu____26563  ->
                       let uu____26564 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26566 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26564 uu____26566)
                   in
                giveup env uu____26556 orig)
             else
               (let uu____26571 =
                  FStar_List.fold_left2
                    (fun uu____26592  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26592 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26613 =
                                 let uu____26618 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26619 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26618
                                   FStar_TypeChecker_Common.EQ uu____26619
                                   "effect universes"
                                  in
                               (match uu____26613 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26571 with
                | (univ_sub_probs,wl1) ->
                    let uu____26639 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26639 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26647 =
                           FStar_List.fold_right2
                             (fun uu____26684  ->
                                fun uu____26685  ->
                                  fun uu____26686  ->
                                    match (uu____26684, uu____26685,
                                            uu____26686)
                                    with
                                    | ((a1,uu____26730),(a2,uu____26732),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26765 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26765 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26647 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26792 =
                                  let uu____26795 =
                                    let uu____26798 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26798
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26795
                                   in
                                FStar_List.append univ_sub_probs uu____26792
                                 in
                              let guard =
                                let guard =
                                  let uu____26820 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26820  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3512_26829 = wl3  in
                                {
                                  attempting = (uu___3512_26829.attempting);
                                  wl_deferred = (uu___3512_26829.wl_deferred);
                                  ctr = (uu___3512_26829.ctr);
                                  defer_ok = (uu___3512_26829.defer_ok);
                                  smt_ok = (uu___3512_26829.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3512_26829.umax_heuristic_ok);
                                  tcenv = (uu___3512_26829.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26831 = attempt sub_probs wl5  in
                              solve env uu____26831))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26849 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26849
           then
             let uu____26854 =
               let uu____26856 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26856
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26858 =
               let uu____26860 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26860
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26854 uu____26858
           else ());
          (let uu____26865 =
             let uu____26870 =
               let uu____26875 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26875
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26870
               (fun uu____26892  ->
                  match uu____26892 with
                  | (c,g) ->
                      let uu____26903 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26903, g))
              in
           match uu____26865 with
           | (c12,g_lift) ->
               ((let uu____26907 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26907
                 then
                   let uu____26912 =
                     let uu____26914 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26914
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26916 =
                     let uu____26918 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26918
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26912 uu____26916
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3532_26928 = wl  in
                     {
                       attempting = (uu___3532_26928.attempting);
                       wl_deferred = (uu___3532_26928.wl_deferred);
                       ctr = (uu___3532_26928.ctr);
                       defer_ok = (uu___3532_26928.defer_ok);
                       smt_ok = (uu___3532_26928.smt_ok);
                       umax_heuristic_ok =
                         (uu___3532_26928.umax_heuristic_ok);
                       tcenv = (uu___3532_26928.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26929 =
                     let rec is_uvar1 t =
                       let uu____26943 =
                         let uu____26944 = FStar_Syntax_Subst.compress t  in
                         uu____26944.FStar_Syntax_Syntax.n  in
                       match uu____26943 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26948 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____26963) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____26969) ->
                           is_uvar1 t1
                       | uu____26994 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27028  ->
                          fun uu____27029  ->
                            fun uu____27030  ->
                              match (uu____27028, uu____27029, uu____27030)
                              with
                              | ((a1,uu____27074),(a2,uu____27076),(is_sub_probs,wl2))
                                  ->
                                  let uu____27109 = is_uvar1 a1  in
                                  if uu____27109
                                  then
                                    ((let uu____27119 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27119
                                      then
                                        let uu____27124 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27126 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27124 uu____27126
                                      else ());
                                     (let uu____27131 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27131 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26929 with
                   | (is_sub_probs,wl2) ->
                       let uu____27159 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27159 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27167 =
                              let uu____27172 =
                                let uu____27173 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27173
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27172
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27167 with
                             | (uu____27180,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27191 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27193 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27191 s uu____27193
                                    in
                                 let uu____27196 =
                                   let uu____27225 =
                                     let uu____27226 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27226.FStar_Syntax_Syntax.n  in
                                   match uu____27225 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27286 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27286 with
                                        | (bs',c3) ->
                                            let a = FStar_List.hd bs'  in
                                            let bs1 = FStar_List.tail bs'  in
                                            let uu____27349 =
                                              let uu____27368 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27368
                                                (fun uu____27472  ->
                                                   match uu____27472 with
                                                   | (l1,l2) ->
                                                       let uu____27545 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27545))
                                               in
                                            (match uu____27349 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27650 ->
                                       let uu____27651 =
                                         let uu____27657 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27657)
                                          in
                                       FStar_Errors.raise_error uu____27651 r
                                    in
                                 (match uu____27196 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27733 =
                                        let uu____27740 =
                                          let uu____27741 =
                                            let uu____27742 =
                                              let uu____27749 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27749,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27742
                                             in
                                          [uu____27741]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27740
                                          (fun b  ->
                                             let uu____27765 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27767 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27769 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27765 uu____27767
                                               uu____27769) r
                                         in
                                      (match uu____27733 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27779 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27779
                                             then
                                               let uu____27784 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27793 =
                                                          let uu____27795 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27795
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27793) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27784
                                             else ());
                                            (let wl4 =
                                               let uu___3604_27803 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3604_27803.attempting);
                                                 wl_deferred =
                                                   (uu___3604_27803.wl_deferred);
                                                 ctr = (uu___3604_27803.ctr);
                                                 defer_ok =
                                                   (uu___3604_27803.defer_ok);
                                                 smt_ok =
                                                   (uu___3604_27803.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3604_27803.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3604_27803.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27828 =
                                                        let uu____27835 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27835, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27828) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27852 =
                                               let f_sort_is =
                                                 let uu____27862 =
                                                   let uu____27863 =
                                                     let uu____27866 =
                                                       let uu____27867 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27867.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27866
                                                      in
                                                   uu____27863.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27862 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27878,uu____27879::is)
                                                     ->
                                                     let uu____27921 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____27921
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____27954 ->
                                                     let uu____27955 =
                                                       let uu____27961 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____27961)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____27955 r
                                                  in
                                               let uu____27967 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28002  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28002
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28023 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28023
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____27967
                                                in
                                             match uu____27852 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28048 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28048
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28049 =
                                                   let g_sort_is =
                                                     let uu____28059 =
                                                       let uu____28060 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28060.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28059 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28065,uu____28066::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28126 ->
                                                         let uu____28127 =
                                                           let uu____28133 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28133)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28127 r
                                                      in
                                                   let uu____28139 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28174  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28174
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28195
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28195
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28139
                                                    in
                                                 (match uu____28049 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28222 =
                                                          let uu____28227 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28228 =
                                                            let uu____28229 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28229
                                                             in
                                                          (uu____28227,
                                                            uu____28228)
                                                           in
                                                        match uu____28222
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28257 =
                                                          let uu____28260 =
                                                            let uu____28263 =
                                                              let uu____28266
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28266
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28263
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28260
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28257
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28290 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28290
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
                                                        let uu____28301 =
                                                          let uu____28304 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28307  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28307)
                                                            uu____28304
                                                           in
                                                        solve_prob orig
                                                          uu____28301 [] wl6
                                                         in
                                                      let uu____28308 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28308))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28331 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28333 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28333]
              | x -> x  in
            let c12 =
              let uu___3670_28336 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3670_28336.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3670_28336.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3670_28336.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3670_28336.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28337 =
              let uu____28342 =
                FStar_All.pipe_right
                  (let uu___3673_28344 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3673_28344.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3673_28344.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3673_28344.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3673_28344.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28342
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28337
              (fun uu____28358  ->
                 match uu____28358 with
                 | (c,g) ->
                     let uu____28365 =
                       let uu____28367 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28367  in
                     if uu____28365
                     then
                       let uu____28370 =
                         let uu____28376 =
                           let uu____28378 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28380 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28378 uu____28380
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28376)
                          in
                       FStar_Errors.raise_error uu____28370 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28386 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28386
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28392 = lift_c1 ()  in
               solve_eq uu____28392 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28401  ->
                         match uu___31_28401 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28406 -> false))
                  in
               let uu____28408 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28438)::uu____28439,(wp2,uu____28441)::uu____28442)
                     -> (wp1, wp2)
                 | uu____28515 ->
                     let uu____28540 =
                       let uu____28546 =
                         let uu____28548 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28550 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28548 uu____28550
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28546)
                        in
                     FStar_Errors.raise_error uu____28540
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28408 with
               | (wpc1,wpc2) ->
                   let uu____28560 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28560
                   then
                     let uu____28563 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28563 wl
                   else
                     (let uu____28567 =
                        let uu____28574 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28574  in
                      match uu____28567 with
                      | (c2_decl,qualifiers) ->
                          let uu____28595 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28595
                          then
                            let c1_repr =
                              let uu____28602 =
                                let uu____28603 =
                                  let uu____28604 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28604  in
                                let uu____28605 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28603 uu____28605
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28602
                               in
                            let c2_repr =
                              let uu____28608 =
                                let uu____28609 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28610 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28609 uu____28610
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28608
                               in
                            let uu____28612 =
                              let uu____28617 =
                                let uu____28619 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28621 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28619
                                  uu____28621
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28617
                               in
                            (match uu____28612 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28627 = attempt [prob] wl2  in
                                 solve env uu____28627)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28647 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28647
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28670 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28670
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
                                        let uu____28680 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28680 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28687 =
                                        let uu____28694 =
                                          let uu____28695 =
                                            let uu____28712 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28715 =
                                              let uu____28726 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28726; wpc1_2]  in
                                            (uu____28712, uu____28715)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28695
                                           in
                                        FStar_Syntax_Syntax.mk uu____28694
                                         in
                                      uu____28687
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
                                     let uu____28775 =
                                       let uu____28782 =
                                         let uu____28783 =
                                           let uu____28800 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28803 =
                                             let uu____28814 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28823 =
                                               let uu____28834 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28834; wpc1_2]  in
                                             uu____28814 :: uu____28823  in
                                           (uu____28800, uu____28803)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28783
                                          in
                                       FStar_Syntax_Syntax.mk uu____28782  in
                                     uu____28775 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28888 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28888
                              then
                                let uu____28893 =
                                  let uu____28895 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28895
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28893
                              else ());
                             (let uu____28899 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28899 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28908 =
                                      let uu____28911 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _28914  ->
                                           FStar_Pervasives_Native.Some
                                             _28914) uu____28911
                                       in
                                    solve_prob orig uu____28908 [] wl1  in
                                  let uu____28915 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28915))))
           in
        let uu____28916 = FStar_Util.physical_equality c1 c2  in
        if uu____28916
        then
          let uu____28919 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28919
        else
          ((let uu____28923 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28923
            then
              let uu____28928 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28930 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28928
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28930
            else ());
           (let uu____28935 =
              let uu____28944 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28947 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28944, uu____28947)  in
            match uu____28935 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28965),FStar_Syntax_Syntax.Total
                    (t2,uu____28967)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____28984 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28984 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28986,FStar_Syntax_Syntax.Total uu____28987) ->
                     let uu____29004 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29004 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29008),FStar_Syntax_Syntax.Total
                    (t2,uu____29010)) ->
                     let uu____29027 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29027 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29030),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29032)) ->
                     let uu____29049 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29049 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29052),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29054)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29071 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29071 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29074),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29076)) ->
                     let uu____29093 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29093 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29096,FStar_Syntax_Syntax.Comp uu____29097) ->
                     let uu____29106 =
                       let uu___3797_29109 = problem  in
                       let uu____29112 =
                         let uu____29113 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29113
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3797_29109.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29112;
                         FStar_TypeChecker_Common.relation =
                           (uu___3797_29109.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3797_29109.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3797_29109.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3797_29109.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3797_29109.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3797_29109.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3797_29109.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3797_29109.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29106 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29114,FStar_Syntax_Syntax.Comp uu____29115) ->
                     let uu____29124 =
                       let uu___3797_29127 = problem  in
                       let uu____29130 =
                         let uu____29131 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29131
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3797_29127.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29130;
                         FStar_TypeChecker_Common.relation =
                           (uu___3797_29127.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3797_29127.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3797_29127.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3797_29127.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3797_29127.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3797_29127.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3797_29127.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3797_29127.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29124 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29132,FStar_Syntax_Syntax.GTotal uu____29133) ->
                     let uu____29142 =
                       let uu___3809_29145 = problem  in
                       let uu____29148 =
                         let uu____29149 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29149
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3809_29145.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3809_29145.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3809_29145.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29148;
                         FStar_TypeChecker_Common.element =
                           (uu___3809_29145.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3809_29145.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3809_29145.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3809_29145.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3809_29145.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3809_29145.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29142 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29150,FStar_Syntax_Syntax.Total uu____29151) ->
                     let uu____29160 =
                       let uu___3809_29163 = problem  in
                       let uu____29166 =
                         let uu____29167 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29167
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3809_29163.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3809_29163.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3809_29163.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29166;
                         FStar_TypeChecker_Common.element =
                           (uu___3809_29163.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3809_29163.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3809_29163.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3809_29163.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3809_29163.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3809_29163.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29160 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29168,FStar_Syntax_Syntax.Comp uu____29169) ->
                     let uu____29170 =
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
                     if uu____29170
                     then
                       let uu____29173 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29173 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29180 =
                            let uu____29185 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29185
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29194 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29195 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29194, uu____29195))
                             in
                          match uu____29180 with
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
                           (let uu____29203 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29203
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29211 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29211 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29214 =
                                  mklstr
                                    (fun uu____29221  ->
                                       let uu____29222 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29224 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29222 uu____29224)
                                   in
                                giveup env uu____29214 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29235 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29235 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29285 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29285 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29310 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29341  ->
                match uu____29341 with
                | (u1,u2) ->
                    let uu____29349 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29351 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29349 uu____29351))
         in
      FStar_All.pipe_right uu____29310 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29388,[])) when
          let uu____29415 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29415 -> "{}"
      | uu____29418 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29445 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29445
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29457 =
              FStar_List.map
                (fun uu____29470  ->
                   match uu____29470 with
                   | (uu____29477,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29457 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29488 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29488 imps
  
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
                  let uu____29545 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29545
                  then
                    let uu____29553 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29555 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29553
                      (rel_to_string rel) uu____29555
                  else "TOP"  in
                let uu____29561 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29561 with
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
              let uu____29621 =
                let uu____29624 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29627  -> FStar_Pervasives_Native.Some _29627)
                  uu____29624
                 in
              FStar_Syntax_Syntax.new_bv uu____29621 t1  in
            let uu____29628 =
              let uu____29633 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29633
               in
            match uu____29628 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29691 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29691
         then
           let uu____29696 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29696
         else ());
        (let uu____29703 =
           FStar_Util.record_time (fun uu____29710  -> solve env probs)  in
         match uu____29703 with
         | (sol,ms) ->
             ((let uu____29722 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29722
               then
                 let uu____29727 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29727
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29740 =
                     FStar_Util.record_time
                       (fun uu____29747  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29740 with
                    | ((),ms1) ->
                        ((let uu____29758 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29758
                          then
                            let uu____29763 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29763
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29775 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29775
                     then
                       let uu____29782 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29782
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
          ((let uu____29808 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29808
            then
              let uu____29813 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29813
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29821 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29821
             then
               let uu____29826 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29826
             else ());
            (let f2 =
               let uu____29832 =
                 let uu____29833 = FStar_Syntax_Util.unmeta f1  in
                 uu____29833.FStar_Syntax_Syntax.n  in
               match uu____29832 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29837 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3926_29838 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3926_29838.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3926_29838.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3926_29838.FStar_TypeChecker_Common.implicits)
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
            let uu____29881 =
              let uu____29882 =
                let uu____29883 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29884  ->
                       FStar_TypeChecker_Common.NonTrivial _29884)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29883;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29882  in
            FStar_All.pipe_left
              (fun _29891  -> FStar_Pervasives_Native.Some _29891)
              uu____29881
  
let with_guard_no_simp :
  'Auu____29901 .
    'Auu____29901 ->
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
            let uu____29941 =
              let uu____29942 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29943  -> FStar_TypeChecker_Common.NonTrivial _29943)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29942;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____29941
  
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
          (let uu____29976 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____29976
           then
             let uu____29981 = FStar_Syntax_Print.term_to_string t1  in
             let uu____29983 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____29981
               uu____29983
           else ());
          (let uu____29988 =
             let uu____29993 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____29993
              in
           match uu____29988 with
           | (prob,wl) ->
               let g =
                 let uu____30001 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30009  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30001  in
               ((let uu____30027 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30027
                 then
                   let uu____30032 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30032
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
        let uu____30053 = try_teq true env t1 t2  in
        match uu____30053 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30058 = FStar_TypeChecker_Env.get_range env  in
              let uu____30059 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30058 uu____30059);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30067 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30067
              then
                let uu____30072 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30074 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30076 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30072
                  uu____30074 uu____30076
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
        (let uu____30100 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30100
         then
           let uu____30105 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30107 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30105
             uu____30107
         else ());
        (let uu____30112 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30112 with
         | (prob,x,wl) ->
             let g =
               let uu____30127 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30136  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30127  in
             ((let uu____30154 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30154
               then
                 let uu____30159 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30159
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30167 =
                     let uu____30168 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30168 g1  in
                   FStar_Pervasives_Native.Some uu____30167)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30190 = FStar_TypeChecker_Env.get_range env  in
          let uu____30191 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30190 uu____30191
  
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
        (let uu____30220 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30220
         then
           let uu____30225 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30227 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30225 uu____30227
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30238 =
           let uu____30245 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30245 "sub_comp"
            in
         match uu____30238 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30258 =
                 FStar_Util.record_time
                   (fun uu____30270  ->
                      let uu____30271 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30280  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30271)
                  in
               match uu____30258 with
               | (r,ms) ->
                   ((let uu____30308 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30308
                     then
                       let uu____30313 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30315 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30317 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30313 uu____30315
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30317
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
      fun uu____30355  ->
        match uu____30355 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30398 =
                 let uu____30404 =
                   let uu____30406 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30408 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30406 uu____30408
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30404)  in
               let uu____30412 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30398 uu____30412)
               in
            let equiv1 v1 v' =
              let uu____30425 =
                let uu____30430 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30431 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30430, uu____30431)  in
              match uu____30425 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30451 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____30482 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30482 with
                      | FStar_Syntax_Syntax.U_unif uu____30489 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30518  ->
                                    match uu____30518 with
                                    | (u,v') ->
                                        let uu____30527 = equiv1 v1 v'  in
                                        if uu____30527
                                        then
                                          let uu____30532 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30532 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____30553 -> []))
               in
            let uu____30558 =
              let wl =
                let uu___4037_30562 = empty_worklist env  in
                {
                  attempting = (uu___4037_30562.attempting);
                  wl_deferred = (uu___4037_30562.wl_deferred);
                  ctr = (uu___4037_30562.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4037_30562.smt_ok);
                  umax_heuristic_ok = (uu___4037_30562.umax_heuristic_ok);
                  tcenv = (uu___4037_30562.tcenv);
                  wl_implicits = (uu___4037_30562.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30581  ->
                      match uu____30581 with
                      | (lb,v1) ->
                          let uu____30588 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30588 with
                           | USolved wl1 -> ()
                           | uu____30591 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30602 =
              match uu____30602 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30614) -> true
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
                      uu____30638,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30640,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30651) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30659,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30668 -> false)
               in
            let uu____30674 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30691  ->
                      match uu____30691 with
                      | (u,v1) ->
                          let uu____30699 = check_ineq (u, v1)  in
                          if uu____30699
                          then true
                          else
                            ((let uu____30707 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30707
                              then
                                let uu____30712 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30714 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30712
                                  uu____30714
                              else ());
                             false)))
               in
            if uu____30674
            then ()
            else
              ((let uu____30724 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30724
                then
                  ((let uu____30730 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30730);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30742 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30742))
                else ());
               (let uu____30755 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30755))
  
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
        let fail1 uu____30828 =
          match uu____30828 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4114_30851 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4114_30851.attempting);
            wl_deferred = (uu___4114_30851.wl_deferred);
            ctr = (uu___4114_30851.ctr);
            defer_ok;
            smt_ok = (uu___4114_30851.smt_ok);
            umax_heuristic_ok = (uu___4114_30851.umax_heuristic_ok);
            tcenv = (uu___4114_30851.tcenv);
            wl_implicits = (uu___4114_30851.wl_implicits)
          }  in
        (let uu____30854 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30854
         then
           let uu____30859 = FStar_Util.string_of_bool defer_ok  in
           let uu____30861 = wl_to_string wl  in
           let uu____30863 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30859 uu____30861 uu____30863
         else ());
        (let g1 =
           let uu____30869 = solve_and_commit env wl fail1  in
           match uu____30869 with
           | FStar_Pervasives_Native.Some
               (uu____30876::uu____30877,uu____30878) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4129_30907 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4129_30907.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4129_30907.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30908 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4134_30917 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4134_30917.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4134_30917.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4134_30917.FStar_TypeChecker_Common.implicits)
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
            let uu___4146_30994 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4146_30994.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4146_30994.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4146_30994.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____30995 =
            let uu____30997 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____30997  in
          if uu____30995
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____31009 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____31010 =
                       let uu____31012 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____31012
                        in
                     FStar_Errors.diag uu____31009 uu____31010)
                  else ();
                  (let vc1 =
                     let uu____31018 =
                       let uu____31022 =
                         let uu____31024 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____31024  in
                       FStar_Pervasives_Native.Some uu____31022  in
                     FStar_Profiling.profile
                       (fun uu____31027  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____31018 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug1
                   then
                     (let uu____31031 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31032 =
                        let uu____31034 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31034
                         in
                      FStar_Errors.diag uu____31031 uu____31032)
                   else ();
                   (let uu____31040 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31040
                      "discharge_guard'" env vc1);
                   (let uu____31042 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31042 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____31051 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31052 =
                                let uu____31054 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31054
                                 in
                              FStar_Errors.diag uu____31051 uu____31052)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____31064 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31065 =
                                let uu____31067 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31067
                                 in
                              FStar_Errors.diag uu____31064 uu____31065)
                           else ();
                           (let vcs =
                              let uu____31081 = FStar_Options.use_tactics ()
                                 in
                              if uu____31081
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31103  ->
                                     (let uu____31105 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____31105);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31149  ->
                                              match uu____31149 with
                                              | (env1,goal,opts) ->
                                                  let uu____31165 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31165, opts)))))
                              else
                                (let uu____31169 =
                                   let uu____31176 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31176)  in
                                 [uu____31169])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31209  ->
                                    match uu____31209 with
                                    | (env1,goal,opts) ->
                                        let uu____31219 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31219 with
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
                                                (let uu____31230 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31231 =
                                                   let uu____31233 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31235 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31233 uu____31235
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31230 uu____31231)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____31242 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31243 =
                                                   let uu____31245 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31245
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31242 uu____31243)
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
      let uu____31263 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31263 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31272 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31272
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31286 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31286 with
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
        let uu____31316 = try_teq false env t1 t2  in
        match uu____31316 with
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
            let uu____31360 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31360 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31373 ->
                     let uu____31386 =
                       let uu____31387 = FStar_Syntax_Subst.compress r  in
                       uu____31387.FStar_Syntax_Syntax.n  in
                     (match uu____31386 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31392) ->
                          unresolved ctx_u'
                      | uu____31409 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31433 = acc  in
            match uu____31433 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____31452 = hd1  in
                     (match uu____31452 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____31463 = unresolved ctx_u  in
                             if uu____31463
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
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
                                       let uu___4259_31510 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4259_31510.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4259_31510.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4259_31510.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4259_31510.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4259_31510.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4259_31510.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4259_31510.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4262_31518 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4262_31518.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4262_31518.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4262_31518.FStar_TypeChecker_Common.imp_range)
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
                                    let uu___4266_31529 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4266_31529.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4266_31529.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4266_31529.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4266_31529.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4266_31529.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4266_31529.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4266_31529.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4266_31529.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4266_31529.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4266_31529.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4266_31529.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4266_31529.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4266_31529.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4266_31529.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4266_31529.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4266_31529.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4266_31529.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4266_31529.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4266_31529.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4266_31529.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4266_31529.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4266_31529.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4266_31529.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4266_31529.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4266_31529.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4266_31529.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4266_31529.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4266_31529.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4266_31529.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4266_31529.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4266_31529.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4266_31529.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4266_31529.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4266_31529.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4266_31529.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4266_31529.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4266_31529.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4266_31529.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4266_31529.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4266_31529.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4266_31529.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4266_31529.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4266_31529.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4266_31529.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4266_31529.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4266_31529.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4271_31534 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4271_31534.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4271_31534.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4271_31534.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4271_31534.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4271_31534.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4271_31534.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4271_31534.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4271_31534.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4271_31534.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4271_31534.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4271_31534.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4271_31534.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4271_31534.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4271_31534.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4271_31534.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4271_31534.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4271_31534.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4271_31534.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4271_31534.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4271_31534.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4271_31534.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4271_31534.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4271_31534.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4271_31534.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4271_31534.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4271_31534.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4271_31534.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4271_31534.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4271_31534.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4271_31534.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4271_31534.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4271_31534.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4271_31534.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4271_31534.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4271_31534.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4271_31534.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4271_31534.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4271_31534.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4271_31534.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4271_31534.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4271_31534.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4271_31534.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4271_31534.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4271_31534.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4271_31534.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4271_31534.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31539 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31539
                                   then
                                     let uu____31544 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31546 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31548 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31550 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31544 uu____31546 uu____31548
                                       reason uu____31550
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4277_31557  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31564 =
                                             let uu____31574 =
                                               let uu____31582 =
                                                 let uu____31584 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31586 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31588 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31584 uu____31586
                                                   uu____31588
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31582, r)
                                                in
                                             [uu____31574]  in
                                           FStar_Errors.add_errors
                                             uu____31564);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31607 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31618  ->
                                               let uu____31619 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31621 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31623 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31619 uu____31621
                                                 reason uu____31623)) env2 g1
                                         true
                                        in
                                     match uu____31607 with
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
          let uu___4289_31631 = g  in
          let uu____31632 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4289_31631.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4289_31631.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4289_31631.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31632
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
        let uu____31672 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31672 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31673 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31673
      | imp::uu____31675 ->
          let uu____31678 =
            let uu____31684 =
              let uu____31686 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31688 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31686 uu____31688
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31684)
             in
          FStar_Errors.raise_error uu____31678
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31708 = teq env t1 t2  in
        force_trivial_guard env uu____31708
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31727 = teq_nosmt env t1 t2  in
        match uu____31727 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4314_31746 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4314_31746.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4314_31746.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4314_31746.FStar_TypeChecker_Common.implicits)
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
        (let uu____31782 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31782
         then
           let uu____31787 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31789 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31787
             uu____31789
         else ());
        (let uu____31794 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31794 with
         | (prob,x,wl) ->
             let g =
               let uu____31813 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31822  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31813  in
             ((let uu____31840 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31840
               then
                 let uu____31845 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31847 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31849 =
                   let uu____31851 = FStar_Util.must g  in
                   guard_to_string env uu____31851  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31845 uu____31847 uu____31849
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
        let uu____31888 = check_subtyping env t1 t2  in
        match uu____31888 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31907 =
              let uu____31908 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31908 g  in
            FStar_Pervasives_Native.Some uu____31907
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31927 = check_subtyping env t1 t2  in
        match uu____31927 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31946 =
              let uu____31947 =
                let uu____31948 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31948]  in
              FStar_TypeChecker_Env.close_guard env uu____31947 g  in
            FStar_Pervasives_Native.Some uu____31946
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____31986 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31986
         then
           let uu____31991 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31993 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____31991
             uu____31993
         else ());
        (let uu____31998 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31998 with
         | (prob,x,wl) ->
             let g =
               let uu____32013 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32022  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32013  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32043 =
                      let uu____32044 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32044]  in
                    FStar_TypeChecker_Env.close_guard env uu____32043 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32085 = subtype_nosmt env t1 t2  in
        match uu____32085 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  